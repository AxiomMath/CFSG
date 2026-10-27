module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbr
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDB17_three_dvd_J (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    3 ∣ Nat.card ↥(qtwoDelJ ψ c) := by
  classical
  have hcard_le : ({a, b, c} : Finset (Fin m)).card ≤ 3 := Finset.card_le_three
  have hlt : ({a, b, c} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hka : k ≠ a := fun h => hk (by simp [h])
  have hkb : k ≠ b := fun h => hk (by simp [h])
  have hkc : k ≠ c := fun h => hk (by simp [h])
  have hsub : ({a, b, k} : Finset (Fin m)) ⊆ Finset.univ.erase c := by
    intro i hi
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ i⟩
    intro hic
    rw [hic] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    tauto
  have hmono : coordBlockSU F0 2 1 ({a, b, k} : Finset (Fin m)) ≤
      coordBlockSU F0 2 1 (Finset.univ.erase c) := by
    intro gr hg
    rw [mem_coordBlockSU_iff] at hg ⊢
    intro i j hij
    exact hg i j (by
      rcases hij with h | h
      · exact Or.inl fun hmem => h (hsub hmem)
      · exact Or.inr fun hmem => h (hsub hmem))
  have hcard216 : Nat.card ↥((coordBlockSU F0 2 1 ({a, b, k} : Finset (Fin m))).map ψ) = 216 :=
    ggQTwoDUnit_card_map_coordBlockSU_three hbase.card_field ψ hbase.hyp.ker hbase.hyp.four_le
      hab hkb.symm hka.symm
  have hdvd216 : 3 ∣ Nat.card ↥((coordBlockSU F0 2 1 ({a, b, k} : Finset (Fin m))).map ψ) := by
    rw [hcard216]; norm_num
  have hdvdJ : Nat.card ↥((coordBlockSU F0 2 1 ({a, b, k} : Finset (Fin m))).map ψ) ∣
      Nat.card ↥(qtwoDelJ ψ c) :=
    Subgroup.card_dvd_of_le (Subgroup.map_mono hmono)
  exact hdvd216.trans hdvdJ

theorem qtwoDB17_map_conj_le (H J₀ : Subgroup G) {n : G} (hn : n ∈ H) :
    (⨆ (a : G) (_ : a ∈ H), J₀.map (MulAut.conj a⁻¹).toMonoidHom).map
      (MulAut.conj n).toMonoidHom ≤
      ⨆ (a : G) (_ : a ∈ H), J₀.map (MulAut.conj a⁻¹).toMonoidHom := by
  rw [Subgroup.map_iSup]
  refine iSup_le fun a => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ha => ?_
  rw [Subgroup.map_map]
  refine le_iSup₂_of_le (a * n⁻¹) (H.mul_mem ha (H.inv_mem hn)) (le_of_eq ?_)
  congr 1
  ext z
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, mul_inv_rev, inv_inv]
  group

theorem qtwoDB17_normalizer_iSup_conj (H J₀ : Subgroup G) :
    H ≤ Subgroup.normalizer
      ((⨆ (a : G) (_ : a ∈ H), J₀.map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hk
    exact qtwoDB17_map_conj_le H J₀ hn hmem
  · intro hk
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj n⁻¹).toMonoidHom hk
    have hback := qtwoDB17_map_conj_le H J₀ (H.inv_mem hn) hmem
    have heq : (MulAut.conj n⁻¹).toMonoidHom (n * k * n⁻¹) = k := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [heq] at hback

theorem qtwoDB17_layer_closure
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N) :
    N ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer 3
        (Subgroup.centralizer ({(b' : G)} : Set G))),
      (qtwoDelJ ψ c).map (MulAut.conj a⁻¹).toMonoidHom := by
  classical
  let Y : Subgroup G := Subgroup.centralizer ({(b' : G)} : Set G)
  have hN' : LargeEvenPComponent 3 Y N := hN
  let J₁ : Subgroup G := qtwoDelJ ψ c
  have hJ₁N : J₁ ≤ N := hJ₁
  let K : Subgroup G := ⨆ (a : G) (_ : a ∈ N), J₁.map (MulAut.conj a⁻¹).toMonoidHom
  have hJK : J₁ ≤ K := by
    have h1 : MulAut.conj ((1 : G)⁻¹) = (1 : MulAut G) := by
      rw [inv_one]; exact map_one (MulAut.conj : G →* MulAut G)
    have h := le_iSup₂ (f := fun (a : G) (_ : a ∈ N) =>
      J₁.map (MulAut.conj a⁻¹).toMonoidHom) (1 : G) (Subgroup.one_mem N)
    rw [h1] at h
    have h2 : J₁.map ((1 : MulAut G).toMonoidHom) = J₁ := by
      rw [show ((1 : MulAut G).toMonoidHom) = MonoidHom.id G from by ext z; rfl,
        Subgroup.map_id]
    rwa [h2] at h
  have hKN : K ≤ N := by
    refine iSup₂_le fun n hn => Subgroup.map_le_iff_le_comap.mpr fun j hj => ?_
    rw [Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact N.mul_mem (N.mul_mem (N.inv_mem hn) (hJ₁N hj)) hn
  have hKnorm : (K.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKN]
    exact qtwoDB17_normalizer_iSup_conj N J₁
  have hNKnorm : N ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp hKnorm
  have hKsub : IsSubnormal K Y := IsSubnormal.step hKN hKnorm hN'.2.1
  let O : Subgroup ↥Y := LargeEvenPPrimeCore 3 ↥Y
  let π : ↥Y →* ↥Y ⧸ O := QuotientGroup.mk' O
  have hOcop : Nat.Coprime 3 (Nat.card ↥O) := CFSG.pPrimeCore_coprime_card
  have hMq : CFSG.Assembly.IsQuasisimple ↥((N.subgroupOf Y).map π) := hN'.2.2.1.2.2
  let MK : Subgroup (↥Y ⧸ O) := (K.subgroupOf Y).map π
  let MN : Subgroup (↥Y ⧸ O) := (N.subgroupOf Y).map π
  have hMKN : MK ≤ MN := Subgroup.map_mono (Subgroup.comap_mono (f := Y.subtype) hKN)
  have hMKnormal : (MK.subgroupOf MN).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMKN]
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hz with ⟨n, hnk, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨k, hkK, rfl⟩
      refine Subgroup.mem_map.mpr ⟨n * k * n⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hnk
        have hkK' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
        simpa using (Subgroup.mem_normalizer_iff.mp (hNKnorm hnN) (k : G)).mp hkK'
      · simp only [map_mul, map_inv]
    · intro hy
      rcases Subgroup.mem_map.mp hz with ⟨n, hnk, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨k, hkK, hk_eq⟩
      refine Subgroup.mem_map.mpr ⟨n⁻¹ * k * n, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hnk
        have hkK' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using
          (Subgroup.mem_normalizer_iff.mp (hNKnorm (N.inv_mem hnN)) (k : G)).mp hkK'
      · rw [map_mul, map_mul, map_inv, hk_eq]
        group
  have hNK : N ≤ K := by
    by_contra hNK'
    have hlt : K < N := lt_of_le_of_ne hKN (fun h => hNK' h.ge)
    exact hN'.2.2.2 K hlt hKsub (by
      haveI : (MK.subgroupOf MN).Normal := hMKnormal
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hMq
        (MK.subgroupOf MN) with hcenter | htop
      · exfalso
        have hJcomp := ggQTwoDUnit_J_comp hcfg (by omega) hbase hcoords hdel.hca hdel.hcb hdel.sign
          hdel.conj hdel.coord hb'B
        have hJY : J₁ ≤ Y := hJcomp.1.1.trans inf_le_left
        haveI : Group.IsPerfect ↥J₁ := ⟨hJcomp.1.2.2.1⟩
        have hJperf : ⁅J₁, J₁⁆ = J₁ := Subgroup.isPerfect_iff.mp inferInstance
        have hJsubY : (J₁.subgroupOf Y) ≤ (K.subgroupOf Y) :=
          Subgroup.comap_mono (f := Y.subtype) hJK
        have hJmapMK : (J₁.subgroupOf Y).map π ≤ MK := Subgroup.map_mono hJsubY
        have hJsubperf : ⁅J₁.subgroupOf Y, J₁.subgroupOf Y⁆ = J₁.subgroupOf Y := by
          apply Subgroup.map_injective Y.subtype_injective
          rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJY, hJperf]
        have hperfπ : ⁅(J₁.subgroupOf Y).map π, (J₁.subgroupOf Y).map π⁆ =
            (J₁.subgroupOf Y).map π := by
          rw [← Subgroup.map_commutator, hJsubperf]
        have hJsubMN : ((J₁.subgroupOf Y).map π).subgroupOf MN ≤ Subgroup.center ↥MN :=
          (Subgroup.comap_mono (f := MN.subtype) hJmapMK).trans hcenter
        have hcomm_all : ∀ w ∈ (J₁.subgroupOf Y).map π, ∀ v ∈ (J₁.subgroupOf Y).map π,
            w * v = v * w := by
          intro w hw v hv
          have hwMN : w ∈ MN := hMKN (hJmapMK hw)
          have hvMN : v ∈ MN := hMKN (hJmapMK hv)
          have hwMK' : (⟨w, hwMN⟩ : ↥MN) ∈ ((J₁.subgroupOf Y).map π).subgroupOf MN := by
            rw [Subgroup.mem_subgroupOf]
            exact hw
          have hw' := hJsubMN hwMK'
          have hcomm := Subgroup.mem_center_iff.mp hw' (⟨v, hvMN⟩ : ↥MN)
          exact (congrArg Subtype.val hcomm).symm
        have hcommπ : ⁅(J₁.subgroupOf Y).map π, (J₁.subgroupOf Y).map π⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun w hw => by
            rw [Subgroup.mem_centralizer_iff]
            intro v hv
            exact (hcomm_all w hw v hv).symm
        have hbot : (J₁.subgroupOf Y).map π = ⊥ := by rw [← hperfπ]; exact hcommπ
        have hleO : J₁.subgroupOf Y ≤ O := by
          have h := hbot
          rw [Subgroup.map_eq_bot_iff] at h
          rwa [QuotientGroup.ker_mk'] at h
        have hcardJ : Nat.card ↥(J₁.subgroupOf Y) = Nat.card ↥J₁ := by
          rw [← Subgroup.card_map_of_injective (f := Y.subtype) Y.subtype_injective,
            Subgroup.map_subgroupOf_eq_of_le hJY]
        have h3 : 3 ∣ Nat.card ↥(J₁.subgroupOf Y) := by
          rw [hcardJ]
          exact qtwoDB17_three_dvd_J (by omega) hbase hdel.hca hdel.hcb hdel.hab
        have hdvd : Nat.card ↥(J₁.subgroupOf Y) ∣ Nat.card ↥O := Subgroup.card_dvd_of_le hleO
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop (h3.trans hdvd)
      · exact le_antisymm hMKN (Subgroup.subgroupOf_eq_top.mp htop))
  have hNLayer : N ≤ LargeEvenPLayer 3 Y := le_sSup hN'
  have hKL3 : K ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer 3 Y),
      J₁.map (MulAut.conj a⁻¹).toMonoidHom := by
    refine iSup₂_le fun n hn => le_iSup₂_of_le n (hNLayer hn) le_rfl
  have hNK' : N ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer 3 Y),
      J₁.map (MulAut.conj a⁻¹).toMonoidHom := (le_antisymm hKN hNK) ▸ hKL3
  simpa [Y, J₁] using hNK'

theorem qtwoDB17_sum_dBasis_eq_one (m : ℕ) :
    (∑ j, dBasis m j) = (1 : DVec m) := by
  funext k
  rw [Finset.sum_apply]
  simp [dBasis, Pi.basisFun_apply, Pi.single_apply]

theorem qtwoDB17_dSign_one_apply (m : ℕ) (a b i : Fin m) :
    dSign m a b (1 : DVec m) i = if i = a ∨ i = b then (-1 : ZMod 3) else 1 := by
  have h1 : (1 : DVec m) = ∑ j, dBasis m j := (qtwoDB17_sum_dBasis_eq_one m).symm
  have hsum : dSign m a b (1 : DVec m) = ∑ j, dSign m a b (dBasis m j) := by
    rw [h1]
    simp only [map_sum]
  rw [hsum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [dSign_apply]
    simp only [Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one]
  · intro j _ hj
    rw [dSign_apply]
    simp [dBasis, Pi.basisFun_apply, Pi.single_apply, Ne.symm hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem qtwoDB17_dSign_mul_self (m : ℕ) (a b : Fin m) :
    dSign m a b * dSign m a b = 1 := by
  refine (dBasis m).ext' fun i => ?_
  rw [LinearEquiv.mul_apply, dSign_apply, map_smul, dSign_apply, smul_smul]
  by_cases h : i = a ∨ i = b <;> simp [h]

theorem qtwoDB17_dSign_invol (m : ℕ) (a b : Fin m) (v : DVec m) :
    dSign m a b (dSign m a b v) = v := by
  have h := congrArg (fun e : DVec m ≃ₗ[ZMod 3] DVec m => e v)
    (qtwoDB17_dSign_mul_self m a b)
  simpa using h

theorem qtwoDB17_map_conj_J_le (hbase : QTwoUnitBase p B Bs x L ψ ε) {s : G}
    (hs : s ∈ Bs) :
    (qtwoDelJ ψ c).map (MulAut.conj s).toMonoidHom ≤ qtwoDelJ ψ c := by
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨g, hgdiag, -, hact⟩ := hbase.diag s hs
  obtain ⟨B, hBA, hBs⟩ := hact A
  change s * ψ A * s⁻¹ ∈ qtwoDelJ ψ c
  rw [hBs]
  refine Subgroup.mem_map.mpr ⟨B, ?_, rfl⟩
  obtain ⟨d, hd⟩ := hgdiag
  rw [mem_coordBlockSU_iff_indicator]
  set Gm : Matrix (Fin m) (Fin m) F0 := ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
    with hGm
  set Gim : Matrix (Fin m) (Fin m) F0 := (((g⁻¹ : GL (Fin m) F0)) : Matrix (Fin m) (Fin m) F0)
    with hGim
  set Am : Matrix (Fin m) (Fin m) F0 := ((A : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
    with hAm
  set P : Matrix (Fin m) (Fin m) F0 := compIndicator F0 (Finset.univ.erase c) with hP
  have hPAm : P * Am = P := (mem_coordBlockSU_iff_indicator.mp hA).1
  have hAmP : Am * P = P := (mem_coordBlockSU_iff_indicator.mp hA).2
  have hGmGim : Gm * Gim = 1 := by
    rw [hGm, hGim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGimGm : Gim * Gm = 1 := by
    rw [hGm, hGim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGmd : Gm = Matrix.diagonal d := by rw [hGm]; exact hd
  have hPcomm : P * Gm = Gm * P := by
    rw [hP, hGmd, compIndicator, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_comm]
  have hPG : P * Gim = Gim * P := by
    calc P * Gim = (Gim * Gm) * P * Gim := by rw [hGimGm, one_mul]
      _ = Gim * (Gm * P) * Gim := by simp only [mul_assoc]
      _ = Gim * (P * Gm) * Gim := by rw [hPcomm]
      _ = Gim * P * (Gm * Gim) := by simp only [mul_assoc]
      _ = Gim * P := by rw [hGmGim, mul_one]
  have hBmat : ((B : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Gm * Am * Gim := by
    have h1 := congrArg (fun z : GL (Fin m) F0 => ((z : Matrix (Fin m) (Fin m) F0))) hBA
    rw [hGm, hAm, hGim]
    simpa [Units.val_mul] using h1
  constructor
  · rw [hBmat]
    calc P * (Gm * Am * Gim) = (P * Gm) * Am * Gim := by simp only [mul_assoc]
      _ = (Gm * P) * Am * Gim := by rw [hPcomm]
      _ = Gm * (P * Am) * Gim := by simp only [mul_assoc]
      _ = Gm * P * Gim := by rw [hPAm]
      _ = Gm * (P * Gim) := by simp only [mul_assoc]
      _ = Gm * (Gim * P) := by rw [hPG]
      _ = (Gm * Gim) * P := by simp only [mul_assoc]
      _ = P := by rw [hGmGim, one_mul]
  · rw [hBmat]
    calc (Gm * Am * Gim) * P = Gm * (Am * (Gim * P)) := by simp only [mul_assoc]
      _ = Gm * (Am * (P * Gim)) := by rw [hPG]
      _ = Gm * ((Am * P) * Gim) := by simp only [mul_assoc]
      _ = Gm * (P * Gim) := by rw [hAmP]
      _ = Gm * (Gim * P) := by rw [hPG]
      _ = (Gm * Gim) * P := by simp only [mul_assoc]
      _ = P := by rw [hGmGim, one_mul]

theorem qtwoDB17_eq_of_mem_closure (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') {k : Fin m} (hkc : k ≠ c) {s : ↥Bs}
    (hs : (s : G) ∈ Subgroup.closure ({x, (b' : G)} : Set G)) :
    βL (Additive.ofMul s) a = βL (Additive.ofMul s) k := by
  classical
  let P : Submodule (ZMod 3) (DVec m) :=
    { carrier := {v : DVec m | v a = v k}
      zero_mem' := rfl
      add_mem' := by
        intro u v hu hv
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        rw [Pi.add_apply, Pi.add_apply, hu, hv]
      smul_mem' := by
        intro r v hv
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [Pi.smul_apply, Pi.smul_apply, hv] }
  let T : Subgroup ↥Bs :=
    { carrier := {t : ↥Bs | βL (Additive.ofMul t) ∈ P}
      one_mem' := by
        show βL (0 : Additive ↥Bs) ∈ P
        rw [map_zero]
        exact P.zero_mem
      mul_mem' := by
        intro u v hu hv
        change βL (Additive.ofMul u + Additive.ofMul v) ∈ P
        rw [map_add]
        exact P.add_mem hu hv
      inv_mem' := by
        intro u hu
        change βL (- Additive.ofMul u) ∈ P
        rw [map_neg]
        exact P.neg_mem hu }
  have hxP : βL (Additive.ofMul (⟨x, hbase.x_mem⟩ : ↥Bs)) ∈ P := by
    change βL (Additive.ofMul (⟨x, hbase.x_mem⟩ : ↥Bs)) a =
      βL (Additive.ofMul (⟨x, hbase.x_mem⟩ : ↥Bs)) k
    rw [hcoords.x_coord hbase.x_mem]
  have hb'P : βL (Additive.ofMul b') ∈ P := by
    change βL (Additive.ofMul b') a = βL (Additive.ofMul b') k
    rw [hdel.coord, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hdel.hca.symm (1 : ZMod 3),
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkc (1 : ZMod 3)]
  have hTK : Subgroup.closure ({x, (b' : G)} : Set G) ≤ T.map (Subgroup.subtype Bs) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hxy | hby
    · rw [hxy]
      exact ⟨⟨x, hbase.x_mem⟩, hxP, rfl⟩
    · rw [hby]
      exact ⟨b', hb'P, rfl⟩
  obtain ⟨u, huT, huG⟩ := hTK hs
  rwa [Subtype.ext huG] at huT

end CFSG.StandardType.QTwo

end
