module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbr
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrBA

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem qtwoDB17_mem_normalizer_map_conj {Bs J : Subgroup G}
    (hBsNormJ₁ : Bs ≤ Subgroup.normalizer (J : Set G)) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) {x : G} (hx : x ∈ Bs) :
    x ∈ Subgroup.normalizer ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  let J₁ : Subgroup G := J
  let J₂ : Subgroup G := J₁.map (MulAut.conj g).toMonoidHom
  have hyBs : g⁻¹ * x * g ∈ Bs :=
    ((Subgroup.mem_normalizer_iff''.mp hgN) x).mp hx
  let yG : G := g⁻¹ * x * g
  have hx_eq : x = g * yG * g⁻¹ := by
    show x = g * (g⁻¹ * x * g) * g⁻¹
    group
  have hyNormJ₁ : yG ∈ Subgroup.normalizer (J₁ : Set G) := hBsNormJ₁ hyBs
  change x ∈ Subgroup.normalizer (J₂ : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨h₁, hh₁, hgh⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨yG * h₁ * yG⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hyNormJ₁ h₁).mp hh₁
    · rw [← hgh, hx_eq]
      change (MulAut.conj g).toMonoidHom (yG * h₁ * yG⁻¹) =
        (MulAut.conj (g * yG * g⁻¹)).toMonoidHom ((MulAut.conj g).toMonoidHom h₁)
      simp [MulAut.conj_apply]
      group
  · intro z hz
    obtain ⟨h₁, hh₁, hgh⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨g * (yG⁻¹ * h₁ * yG) * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨yG⁻¹ * h₁ * yG,
        (Subgroup.mem_normalizer_iff''.mp hyNormJ₁ h₁).mp hh₁,
        by simp [MulAut.conj_apply]⟩
    · rw [← hgh, hx_eq]
      change (MulAut.conj (g * yG * g⁻¹)).toMonoidHom
          (g * (yG⁻¹ * h₁ * yG) * g⁻¹) = (MulAut.conj g).toMonoidHom h₁
      simp [MulAut.conj_apply]
      group

theorem qtwoDB17_innerDiag_of_inner (hsub : GGRawInnSubgroupInput) {B Bs L D J N : Subgroup G}
    {x b' : G} (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hnbr : GGNbr 3 B x D J b' N) (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    (hinner : ∀ s : ↥Bs, ∃ t ∈ N, ∀ n ∈ N, (s : G) * n * (s : G)⁻¹ = t * n * t⁻¹) :
    GGInnerDiagOn Bs N := by
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  have hnbr' : LargeEvenIsNeighborOf 3 B x L b' N := isNeighborOf_of_ggNbr hDJ hnbr
  have hmark5 : LargeEvenMarking N (fun lab R _ I F θ =>
      LargeEvenHalfSplit 3 lab (Subgroup.center N = ⊥) ∨
        LargeEvenPrimeField 3 lab I F
          (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) :=
    (hst.2.2.1 b' N hnbr').2
  have hmark5' : LargeEvenMarking N (fun lab R _ I F θ =>
      (LargeEvenHalfSplit 3 lab (Subgroup.center N = ⊥) ∨
        LargeEvenPrimeField 3 lab I F
          (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) ∧
      GGRawInnSubgroup R I F) :=
    largeEvenMarking_and_labelAll_simple (S := fun _ => True)
      (fun lab hl _ => hsub lab hl) (fun _ _ _ _ _ _ _ => trivial) hmark5
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark5'
  refine ⟨hcomm, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hP5, hsubprop⟩
  refine ⟨hs, hna, θ, hBsN, fun b hb => ?_⟩
  obtain ⟨t, htN, htn⟩ := hinner ⟨b, hb⟩
  let tb : ↥N := ⟨t, htN⟩
  let tbar : R := θ (QuotientGroup.mk tb)
  refine ⟨(MulAut.conj tbar)⁻¹, hsubprop.2.1 _ (hsubprop.2.2 tbar), ?_⟩
  intro l l' hl'
  have hmem : b⁻¹ * (l : G) * b ∈ N :=
    (Subgroup.mem_normalizer_iff''.mp (hBsN hb) (l : G)).mp l.2
  have hkey : (l' : G) = t⁻¹ * (l : G) * t := by
    have h1 := htn (b⁻¹ * (l : G) * b) hmem
    have h3 : (l : G) = t * (b⁻¹ * (l : G) * b) * t⁻¹ := by
      rw [← h1]; group
    have h4 : t⁻¹ * (l : G) * t = b⁻¹ * (l : G) * b := by
      nth_rewrite 1 [h3]
      group
    rw [hl']
    exact h4.symm
  have hl'eq : l' = tb⁻¹ * l * tb := by
    apply Subtype.ext
    simpa using hkey
  have htheta : θ (QuotientGroup.mk l') = (MulAut.conj tbar)⁻¹ (θ (QuotientGroup.mk l)) := by
    rw [hl'eq, ← map_inv (MulAut.conj : R →* MulAut R) tbar, MulAut.conj_apply, inv_inv]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    rfl
  exact htheta.symm


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDB17_Bs_le_normalizer_J (hbase : QTwoUnitBase p B Bs x L ψ ε) :
    Bs ≤ Subgroup.normalizer (qtwoDelJ ψ c : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact qtwoDB17_map_conj_J_le hbase hs
      (Subgroup.mem_map.mpr ⟨h, hh, by simp [MulAut.conj_apply]⟩)
  · intro hh
    have hmem : h = (MulAut.conj s⁻¹).toMonoidHom (s * h * s⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hmem]
    exact qtwoDB17_map_conj_J_le hbase (Subgroup.inv_mem Bs hs)
      (Subgroup.mem_map.mpr ⟨s * h * s⁻¹, hh, rfl⟩)

theorem qtwoDB17_x_mem_normalizer_J₂ (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hdel : QTwoUnitDel Bs βL a b c α g b') :
    x ∈ Subgroup.normalizer
      (((qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
  qtwoDB17_mem_normalizer_map_conj (qtwoDB17_Bs_le_normalizer_J hbase) hdel.norm hbase.x_mem

theorem qtwoDB17_x_not_mem_centralizer_J₂ (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b') :
    x ∉ Subgroup.centralizer
      (((qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  classical
  intro hxcentJ₂
  let J₁ : Subgroup G := qtwoDelJ ψ c
  let J₂ : Subgroup G := J₁.map (MulAut.conj g).toMonoidHom
  have hyBs : g⁻¹ * x * g ∈ Bs :=
    ((Subgroup.mem_normalizer_iff''.mp hdel.norm) x).mp hbase.x_mem
  let yG : G := g⁻¹ * x * g
  let y : ↥Bs := ⟨yG, hyBs⟩
  have hx_eq : x = g * yG * g⁻¹ := by
    show x = g * (g⁻¹ * x * g) * g⁻¹
    group
  have hycentJ₁ : yG ∈ Subgroup.centralizer (J₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h₁ hh₁
    have hmem : g * h₁ * g⁻¹ ∈ J₂ :=
      Subgroup.mem_map.mpr ⟨h₁, hh₁, by simp [MulAut.conj_apply]⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hxcentJ₂) (g * h₁ * g⁻¹) hmem
    calc h₁ * yG = g⁻¹ * ((g * h₁ * g⁻¹) * x) * g := by
          rw [hx_eq]; group
      _ = g⁻¹ * (x * (g * h₁ * g⁻¹)) * g := by rw [hcomm]
      _ = yG * h₁ := by rw [hx_eq]; group
  have hyClosure : yG ∈ Subgroup.closure ({x, (b' : G)} : Set G) := by
    have hcent := ggQTwoDUnit_cent_J (by omega) hbase hcoords hdel.coord
    rw [← hcent]
    exact Subgroup.mem_inf.mpr ⟨hyBs, hycentJ₁⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset (Fin m))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h3 := Finset.card_le_three (a := a) (b := b) (c := c)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hka, hkb, hkc⟩ := hk
  have hval : βL (Additive.ofMul y) a = βL (Additive.ofMul y) k :=
    qtwoDB17_eq_of_mem_closure hbase hcoords hdel hkc hyClosure
  have hβy : βL (Additive.ofMul y) = dSign m a b (1 : DVec m) := by
    have hsign : dSign m a b (βL (Additive.ofMul y)) = (1 : DVec m) := by
      have h1 := hdel.sign y
      rw [← h1]
      have hαy : α y = (⟨x, hbase.x_mem⟩ : ↥Bs) := by
        apply Subtype.ext
        rw [hdel.conj y]
        show g * yG * g⁻¹ = x
        rw [hx_eq]
      rw [hαy]
      exact hcoords.x_coord hbase.x_mem
    have hinvol := qtwoDB17_dSign_invol m a b (βL (Additive.ofMul y))
    rw [hsign] at hinvol
    exact hinvol.symm
  have hval_a : βL (Additive.ofMul y) a = (-1 : ZMod 3) := by
    rw [hβy, qtwoDB17_dSign_one_apply]
    exact if_pos (Or.inl rfl)
  have hval_k : βL (Additive.ofMul y) k = (1 : ZMod 3) := by
    rw [hβy, qtwoDB17_dSign_one_apply]
    exact if_neg (by tauto)
  have hne : (-1 : ZMod 3) ≠ 1 := by decide
  exact hne ((hval_a.symm.trans hval).trans hval_k)

theorem qtwoDB17_not_centralizes
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N) :
    ¬ (⁅N, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf 3 N := by
  classical
  intro hle
  let J₁ : Subgroup G := qtwoDelJ ψ c
  let J₂ : Subgroup G := J₁.map (MulAut.conj g).toMonoidHom
  let O : Subgroup G := LargeEvenPPrimeCoreOf 3 N
  have hJ₂N : J₂ ≤ N := hJ₂
  have hJcomp :=
    ggQTwoDUnit_J_comp hcfg (by omega) hbase hcoords hdel.hca hdel.hcb hdel.sign hdel.conj
    hdel.coord hb'B
  have hJ₂q : CFSG.Assembly.IsQuasisimple J₂ := hJcomp.2.2.2
  have hcardJ₂ : Nat.card ↥J₂ = Nat.card ↥J₁ := by
    change Nat.card ↥(J₁.map (MulAut.conj g).toMonoidHom) = Nat.card ↥J₁
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
  have h3J₂ : 3 ∣ Nat.card ↥J₂ := by
    rw [hcardJ₂]
    exact qtwoDB17_three_dvd_J (by omega) hbase hdel.hca hdel.hcb hdel.hab
  have hOcop : Nat.Coprime 3 (Nat.card ↥O) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : Nat.card ↥O = Nat.card ↥(CFSG.pPrimeCore 3 ↥N) := by
      change Nat.card ↥((CFSG.pPrimeCore 3 ↥N).map N.subtype) =
        Nat.card ↥(CFSG.pPrimeCore 3 ↥N)
      exact Subgroup.card_map_of_injective (f := N.subtype) N.subtype_injective
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  have hNO : N ≤ Subgroup.normalizer (O : Set G) := fun n hn =>
    mem_normalizer_largeEvenPPrimeCoreOf (A := N) (Subgroup.le_normalizer hn)
  have hJ₂normO : J₂ ≤ Subgroup.normalizer (O : Set G) := hJ₂N.trans hNO
  have hxnormJ₂ : x ∈ Subgroup.normalizer (J₂ : Set G) := qtwoDB17_x_mem_normalizer_J₂ hbase hdel
  have hcommJO : (⁅J₂, Subgroup.zpowers x⁆ : Subgroup G) ≤ O :=
    (Subgroup.commutator_mono hJ₂N le_rfl).trans hle
  have hxcentJ₂ : x ∈ Subgroup.centralizer (J₂ : Set G) :=
    mem_centralizer_of_commutator_le_coprime Nat.prime_three hJ₂q h3J₂ hOcop hJ₂normO hxnormJ₂
      hcommJO
  exact qtwoDB17_x_not_mem_centralizer_J₂ (by omega) hbase hcoords hdel hxcentJ₂

theorem ggQTwoDUnit_nbr (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N) :
    GGNbr 3 B x (Subgroup.closure {x, (b' : G)}) (qtwoDelJ ψ c) b' N := by
  have hI : GGThmIHyp 3 B x L := hbase.p_eq ▸ hcfg.1.1.1.1
  have hDJ : LargeEvenStdSub 3 B x L (Subgroup.closure {x, (b' : G)}) (qtwoDelJ ψ c) :=
    ggQTwoDUnit_stdSub hcfg hm hbase hcoords hdel.coord hb'B
  have hpJ : 3 ∣ Nat.card ↥(qtwoDelJ ψ c) :=
    qtwoDB17_three_dvd_J (by omega) hbase hdel.hca hdel.hcb hdel.hab
  exact ggNbr_of_pComponent hI hDJ hpJ rfl hN hJ₁
    (qtwoDB17_layer_closure hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂)
    (qtwoDB17_not_centralizes hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂)

theorem qtwoDB17_innerDiag_of_rawInn (hsub : GGRawInnSubgroupInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N) :
    GGInnerDiagOn Bs N :=
  qtwoDB17_innerDiag_of_inner hsub (hbase.p_eq ▸ hcfg.1.1.1.1)
    (ggQTwoDUnit_stdSub hcfg hm hbase hcoords hdel.coord hb'B)
    (ggQTwoDUnit_nbr hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂)
    (ggQTwoDUnit_normalizer_N (by omega) hbase b'.2 hN hJ₁)
    (ggQTwoDUnit_inner_N (by omega) hbase hcoords hdel hN hJ₁ hJ₂)

theorem ggQTwoDUnit_innerDiag_N
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N) :
    GGInnerDiagOn Bs N :=
  qtwoDB17_innerDiag_of_rawInn (ggRawInnSubgroupInput_of_rawInnField ggRawInnFieldInput_holds)
    hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂

end CFSG.StandardType.QTwo

end
