module

public import CFSG.RankThree.PartTwo.Sec15.F153Leaf
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating10
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofPerm

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.RankThree.PartTwo.Sec15.SimsBaumann (W315 isTwoReducedIn_W315)
open CFSG.RankThree.PartTwo.KFacts.KP2 Equiv

@[expose] def A10NoV4Offender : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H L E : Subgroup (MulAut V), FFHyp H L →
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 10)) →
      E ≤ L → E ≠ ⊥ → CFSG.Quasithin.IsElemAbelian2 E → Nat.card E ≤ 4 →
        Nat.card V > Nat.card E * Nat.card (CFSG.Quasithin.fixV E)

theorem card_le_four_of_le_k {Q : Subgroup (Perm (Fin 10))}
    (h : Q ≤ kOne ∨ Q ≤ kTwo ∨ Q ≤ kThree) :
    Nat.card Q ≤ 4 ∧ ∀ q ∈ Q, q ∈ alternatingGroup (Fin 10) := by
  have hsign := Sec17.Proof171Gen.kF_sign
  have key : ∀ (K : Subgroup (Perm (Fin 10))) (F : Fin 4 → Perm (Fin 10)),
      K = {x | ∃ m, x = F m} → (∀ m, Perm.sign (F m) = 1) → Q ≤ K →
        Nat.card Q ≤ 4 ∧ ∀ q ∈ Q, q ∈ alternatingGroup (Fin 10) := by
    intro K F hK hs hQK
    refine ⟨?_, fun q hq => ?_⟩
    · have hsurj : Function.Surjective (fun m : Fin 4 =>
          (⟨F m, show F m ∈ (K : Set (Perm (Fin 10))) by rw [hK]; exact ⟨m, rfl⟩⟩ : ↥K)) := by
        rintro ⟨x, hx⟩
        have hx' : x ∈ {x | ∃ m, x = F m} := by rw [← hK]; exact hx
        obtain ⟨m, rfl⟩ := hx'
        exact ⟨m, rfl⟩
      calc Nat.card Q ≤ Nat.card K := Subgroup.card_le_of_le hQK
        _ ≤ Nat.card (Fin 4) := Nat.card_le_card_of_surjective _ hsurj
        _ = 4 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 4)
    · have hqK : q ∈ K := hQK hq
      have hqK' : q ∈ {x | ∃ m, x = F m} := by rw [← hK]; exact hqK
      obtain ⟨m, rfl⟩ := hqK'
      exact Perm.mem_alternatingGroup.mpr (hs m)
  rcases h with h | h | h
  · exact key kOne kOneF rfl (fun m => (hsign m).1) h
  · exact key kTwo kTwoF rfl (fun m => (hsign m).2.1) h
  · exact key kThree kThreeF rfl (fun m => (hsign m).2.2) h

theorem a10_internal {V : Type} [CommGroup V] [Finite V] {H L B T : Subgroup (MulAut V)}
    (hFF : FFHyp H L) (e : ↥L ≃* alternatingGroup (Fin 10))
    (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hBL : B ≤ L)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB27 : Nat.card B = 27)
    (hBT : B ≤ Subgroup.normalizer (T : Set (MulAut V))) :
    T ≤ L ∧ Nat.card T ≤ 4 := by
  classical
  have hLF : L = CFSG.Open.quasithinGenFitting H := hFF.1
  have hLH : L ≤ H := by rw [hLF]; exact quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hLF]; exact le_normalizer_quasithinGenFitting H
  have hcent : H ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
    have h := centralizer_quasithinGenFitting_le H
    rw [← hLF] at h
    exact h
  have hZ : Subgroup.center ↥L = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [alternatingGroup.center_eq_bot (by simp)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (show Function.Injective e.toMonoidHom from e.injective)).mp h1
  have hC : ∀ g ∈ H, (∀ l ∈ L, g * l = l * g) → g = 1 := by
    intro g hg hgc
    have hgL : g ∈ L := hcent ⟨hg, Subgroup.mem_centralizer_iff.mpr fun l hl => (hgc l hl).symm⟩
    have hgZ : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hgc l l.2).symm
    rw [hZ, Subgroup.mem_bot] at hgZ
    exact congrArg Subtype.val hgZ
  let cE : Perm (Fin 10) ≃* MulAut (alternatingGroup (Fin 10)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10 (by norm_num)
        (by norm_num))
  have hcE : ∀ σ : Perm (Fin 10), cE σ = MulAut.conjNormal σ := fun σ => rfl
  let c : ↥H →* MulAut ↥L := (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hHN)
  have hc : ∀ (g : ↥H) (l : ↥L),
      ((c g l : ↥L) : MulAut V) = (g : MulAut V) * l * (g : MulAut V)⁻¹ := fun g l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hHN g) l
  let ρ : ↥H →* Perm (Fin 10) :=
    cE.symm.toMonoidHom.comp
      ((MulAut.congr e).toMonoidHom.comp c)
  have hρ : ∀ (g : ↥H) (l : ↥L), (ρ g) * ((e l : alternatingGroup (Fin 10)) : Perm (Fin 10)) *
      (ρ g)⁻¹ = ((e (c g l) : alternatingGroup (Fin 10)) : Perm (Fin 10)) := by
    intro g l
    have h1 : cE (ρ g) = MulAut.congr e (c g) := by
      simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have h2 := congrArg (fun τ : MulAut (alternatingGroup (Fin 10)) =>
      ((τ (e l) : alternatingGroup (Fin 10)) : Perm (Fin 10))) h1
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    rw [hcE, MulAut.conjNormal_apply] at h2
    exact h2
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcomm : ∀ l ∈ L, (g : MulAut V) * l = l * (g : MulAut V) := by
      intro l hl
      have h1 := hρ g ⟨l, hl⟩
      rw [hg, one_mul, inv_one, mul_one] at h1
      have h2 : c g ⟨l, hl⟩ = ⟨l, hl⟩ := e.injective (Subtype.ext h1.symm)
      have h3 := hc g ⟨l, hl⟩
      rw [h2] at h3
      have h4 : (l : MulAut V) = (g : MulAut V) * l * (g : MulAut V)⁻¹ := h3
      calc (g : MulAut V) * l = ((g : MulAut V) * l * (g : MulAut V)⁻¹) * g := by group
        _ = l * g := by rw [← h4]
    exact Subtype.ext (hC g g.2 hcomm)
  have hρL : ∀ (l : MulAut V) (hl : l ∈ L),
      ρ ⟨l, hLH hl⟩ = ((e ⟨l, hl⟩ : alternatingGroup (Fin 10)) : Perm (Fin 10)) := by
    intro l hl
    apply cE.injective
    refine MulEquiv.ext fun a => Subtype.ext ?_
    have ha := hρ ⟨l, hLH hl⟩ (e.symm a)
    rw [MulEquiv.apply_symm_apply] at ha
    have hcl : ((c ⟨l, hLH hl⟩ (e.symm a) : ↥L) : MulAut V) = l * (e.symm a : ↥L) * l⁻¹ :=
      hc ⟨l, hLH hl⟩ (e.symm a)
    have hcl' : c ⟨l, hLH hl⟩ (e.symm a) = ⟨l, hl⟩ * e.symm a * ⟨l, hl⟩⁻¹ := Subtype.ext hcl
    rw [hcl', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at ha
    show ((cE (ρ ⟨l, hLH hl⟩) a : alternatingGroup (Fin 10)) : Perm (Fin 10)) =
      ((cE ((e ⟨l, hl⟩ : alternatingGroup (Fin 10)) : Perm (Fin 10)) a :
        alternatingGroup (Fin 10)) : Perm (Fin 10))
    rw [hcE, MulAut.conjNormal_apply, hcE, MulAut.conjNormal_apply]
    exact ha
  have hBH : B ≤ H := hBL.trans hLH
  set B' : Subgroup ↥H := B.subgroupOf H with hB'
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  have hcardB : Nat.card (B'.map ρ) = 27 := by
    rw [Subgroup.card_map_of_injective hρinj, ← hB27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hcommB : ∀ x ∈ B'.map ρ, ∀ y ∈ B'.map ρ, x * y = y * x := by
    rintro _ ⟨b₁, hb₁, rfl⟩ _ ⟨b₂, hb₂, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hb₁) _
      (Subgroup.mem_subgroupOf.mp hb₂)))
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eTwentySeven hcardB hcommB
  set Q : Subgroup (Perm (Fin 10)) := (T'.map ρ).map (MulAut.conj g).toMonoidHom with hQ
  have hcardQ : Nat.card Q = Nat.card T := by
    rw [hQ, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective hρinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have h3 : ¬ 3 ∣ Nat.card Q := by
    rw [hcardQ]
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hmemQ : ∀ q : Perm (Fin 10), q ∈ Q ↔ g⁻¹ * q * g ∈ T'.map ρ := by
    intro q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h : g⁻¹ * (MulAut.conj g).toMonoidHom x * g = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [h]
      exact hx
    · intro h
      refine ⟨g⁻¹ * q * g, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hnormρ : ∀ b ∈ B', ∀ q : Perm (Fin 10), q ∈ T'.map ρ ↔ ρ b * q * (ρ b)⁻¹ ∈ T'.map ρ := by
    intro b hb q
    have hbT : (b : MulAut V) ∈ Subgroup.normalizer (T : Set (MulAut V)) :=
      hBT (Subgroup.mem_subgroupOf.mp hb)
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨b * t * b⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hbT t).mp (Subgroup.mem_subgroupOf.mp ht))
    · rintro ⟨t, ht, hq⟩
      refine ⟨b⁻¹ * t * b, ?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hbT) t).mp
          (Subgroup.mem_subgroupOf.mp ht)
        exact Subgroup.mem_subgroupOf.mpr (by simpa using h1)
      · rw [map_mul, map_mul, map_inv, hq]
        group
  have hE : eTwentySeven ≤ Subgroup.normalizer (Q : Set (Perm (Fin 10))) := by
    intro z hz
    rw [← hg] at hz
    obtain ⟨y, ⟨b, hb, rfl⟩, rfl⟩ := hz
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hmemQ, hmemQ]
    have key : g⁻¹ * ((MulAut.conj g).toMonoidHom (ρ b) * q *
        ((MulAut.conj g).toMonoidHom (ρ b))⁻¹) * g = ρ b * (g⁻¹ * q * g) * (ρ b)⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [key]
    exact hnormρ b hb _
  have hQK := card_le_four_of_le_k (le_kOne_or_le_kTwo_or_le_kThree h3 hE)
  refine ⟨fun t ht => ?_, hcardQ ▸ hQK.1⟩
  have hρt : ρ ⟨t, hTH ht⟩ ∈ T'.map ρ := ⟨_, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hqQ : MulAut.conj g (ρ ⟨t, hTH ht⟩) ∈ Q := ⟨_, hρt, rfl⟩
  have hA : g * ρ ⟨t, hTH ht⟩ * g⁻¹ ∈ alternatingGroup (Fin 10) := hQK.2 _ hqQ
  have hρA : ρ ⟨t, hTH ht⟩ ∈ alternatingGroup (Fin 10) := by
    have h' := (inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem _ hA g⁻¹
    rwa [show g⁻¹ * (g * ρ ⟨t, hTH ht⟩ * g⁻¹) * g⁻¹⁻¹ = ρ ⟨t, hTH ht⟩ by group] at h'
  obtain ⟨l, hl⟩ := e.surjective ⟨ρ ⟨t, hTH ht⟩, hρA⟩
  have hρl : ρ ⟨l.1, hLH l.2⟩ = ρ ⟨t, hTH ht⟩ := by
    rw [hρL l.1 l.2]
    exact congrArg Subtype.val hl
  have := hρinj hρl
  have hlt : l.1 = t := congrArg Subtype.val this
  rw [← hlt]
  exact l.2

section Factor

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

theorem exists_central_factor_W315' (hS2 : IsPGroup 2 S)
    (hXS : oResidual 2 X ⊔ S = ⊤)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    ∃ h : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) →* ↥(autOn (oResidual 2 X) (W315 X)),
      Function.Surjective h ∧
        h.ker ≤ Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ∧
        ∀ (x : X) (hx : x ∈ oResidual 2 X) (y : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))),
          (y : X ⧸ CFSG.pCore 2 X) = (x : X ⧸ CFSG.pCore 2 X) →
            (h y : MulAut ↥(W315 X)) =
              CFSG.QuasithinUnique.Setup.rho (W315 X) (oResidual 2 X)
                (oResidual_le_normalizer_W315 hq hWL) ⟨x, hx⟩ := by
  classical
  set Q := CFSG.pCore 2 X with hQ
  set L := oResidual 2 X with hL
  set K := oResidual 2 (X ⧸ Q) with hK
  have hLV : L ≤ Subgroup.normalizer (W315 X : Set X) := oResidual_le_normalizer_W315 hq hWL
  have hKeq : K = L.map (QuotientGroup.mk' Q) := oResidual_quotient_eq_map hS2 hXS
  let π : ↥L →* ↥K :=
    ((QuotientGroup.mk' Q).comp L.subtype).codRestrict K (fun l => by
      rw [hKeq]; exact ⟨l, l.2, rfl⟩)
  have hπ : Function.Surjective π := by
    rintro ⟨y, hy⟩
    rw [hKeq] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨⟨l, hl⟩, rfl⟩
  let φ : ↥L →* ↥(autOn L (W315 X)) :=
    (CFSG.QuasithinUnique.Setup.rho (W315 X) L hLV).codRestrict _ fun l =>
      (CFSG.QuasithinUnique.Setup.range_rho hLV).le ⟨l, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [← CFSG.QuasithinUnique.Setup.range_rho hLV] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l, rfl⟩
  have hφ1 : ∀ l : ↥L, φ l = 1 ↔ (l : X) ∈ Subgroup.centralizer (W315 X : Set X) := by
    intro l
    rw [← CFSG.QuasithinUnique.Setup.rho_eq_one_iff hLV l]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hk : π.ker ≤ φ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    rw [hφ1]
    have h1 : QuotientGroup.mk' Q (l : X) = 1 := congrArg Subtype.val hl
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact pCore_le_centralizer_W315 h1
  have hq' := CFSG.HardMathSupport.Cooperstein.Coordinator.isQuasisimple_to_open' hq
  have hLn : L.Normal := Stage1.Thm6.Prod.oResidual_normal 2 X
  have hcen : ∀ a ∈ φ.ker, π a ∈ Subgroup.center ↥K := by
    have hN : (φ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top
      hq'.1 hq'.2 _ hN with hc | htop
    · intro a ha
      exact hc ⟨a, ha, rfl⟩
    · exfalso
      apply hWL
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp ?_)
      intro l hl
      have hmem : π ⟨l, hl⟩ ∈ φ.ker.map π := by rw [htop]; trivial
      obtain ⟨a, ha, hal⟩ := hmem
      have hker : a⁻¹ * ⟨l, hl⟩ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hal, inv_mul_cancel]
      have h2 := hk hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp ha, inv_one, one_mul] at h2
      exact (hφ1 ⟨l, hl⟩).mp h2
  obtain ⟨h, hs, hker, hh⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.exists_central_factor
      π hπ φ hφ hk hcen
  refine ⟨h, hs, hker, fun x hx y hxy => ?_⟩
  have hy : y = π ⟨x, hx⟩ := Subtype.ext hxy
  rw [hy, hh]
  rfl

end Factor

section XLevel

variable {X : Type} [Group X] [Finite X]

theorem false_of_a10_pushing_up (hK10 : A10NoV4Offender)
    (hK : CFSG.Open.IsKGroup X) (hF : generalizedFitting X = CFSG.pCore 2 X)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    {S : Subgroup X} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hQS : CFSG.pCore 2 X ≤ S)
    (hXS : oResidual 2 X ⊔ S = ⊤)
    (hJ : ¬ CFSG.Quasithin.thompsonJ S ≤ CFSG.pCore 2 X)
    (hno : ¬ ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal)
    (ψ : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* alternatingGroup (Fin 10))
    {A : Subgroup X} (hA27 : Nat.card A = 27) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA3 : ∀ x ∈ A, x ^ 3 = 1) (hAS : A ≤ Subgroup.normalizer (S : Set X)) : False := by
  have hWL := comm_W315_ne_bot hF hS2 hS1 hQS hXS hno
  have hred := isTwoReducedIn_W315 hq hWL
  have hV := hred.2.2.1
  have hJC := not_thompsonJ_le_centralizer_W315 hq hS2 hQS hXS hJ hWL
  have hVS : W315 X ≤ S := W315_le_pCore.trans hQS
  have hSN : S ≤ Subgroup.normalizer (W315 X : Set X) := fun s _ => hred.2.1 (Subgroup.mem_top s)
  obtain ⟨Aoff, hAoffS, hA1, hAe, hAoff⟩ := (B2_7_of_not_le hV hVS hSN hJC).1
  have hLN : oResidual 2 X ≤ Subgroup.normalizer (W315 X : Set X) :=
    oResidual_le_normalizer_W315 hq hWL
  have hAL : A ≤ oResidual 2 X := by
    intro x hx
    apply Subgroup.subset_closure
    change Nat.Coprime (orderOf x) 2
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hA3 x hx)) (by norm_num)
  have hAN : A ≤ Subgroup.normalizer (W315 X : Set X) := hAL.trans hLN
  obtain ⟨h, hs, hker, hcompat⟩ := exists_central_factor_W315' hS2 hXS hq hWL
  have hZ : Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) = ⊥ := by
    have h1 := Subgroup.map_center_eq ψ
    rw [alternatingGroup.center_eq_bot (by simp)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (show Function.Injective ψ.toMonoidHom from ψ.injective)).mp h1
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy' := hker (MonoidHom.mem_ker.mpr hy)
    rw [hZ, Subgroup.mem_bot] at hy'
    exact hy'
  let e1 : ↥(autI hV (oResidual 2 X)) ≃* alternatingGroup (Fin 10) :=
    (MulEquiv.ofBijective h ⟨hinj, hs⟩).symm.trans ψ
  have hAC : A ⊓ Subgroup.centralizer (W315 X : Set X) = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haA, haC⟩
    have haL : a ∈ oResidual 2 X := hAL haA
    have hmem : (a : X ⧸ CFSG.pCore 2 X) ∈ oResidual 2 (X ⧸ CFSG.pCore 2 X) := by
      rw [oResidual_quotient_eq_map hS2 hXS]
      exact ⟨a, haL, rfl⟩
    have h1 := hcompat a haL ⟨(a : X ⧸ CFSG.pCore 2 X), hmem⟩ rfl
    have h2 : CFSG.QuasithinUnique.Setup.rho (W315 X) (oResidual 2 X)
        (oResidual_le_normalizer_W315 hq hWL) ⟨a, haL⟩ = 1 :=
      (CFSG.QuasithinUnique.Setup.rho_eq_one_iff (oResidual_le_normalizer_W315 hq hWL)
        ⟨a, haL⟩).mpr haC
    rw [h2] at h1
    have h3 : h ⟨(a : X ⧸ CFSG.pCore 2 X), hmem⟩ = 1 := Subtype.ext h1
    have h4 := hinj (h3.trans (map_one h).symm)
    have h5 : (a : X ⧸ CFSG.pCore 2 X) = 1 := congrArg Subtype.val h4
    rw [QuotientGroup.eq_one_iff] at h5
    have h6 : a ∈ S := hQS h5
    obtain ⟨k, hk⟩ := hS2 ⟨a, h6⟩
    have hk' : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd3 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hA3 a haA)
    have hd2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h7 := Nat.dvd_gcd hd3 hd2
    rw [hcop.gcd_eq_one] at h7
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h7))
  have hB27 : Nat.card (autI hV A) = 27 := by
    have h1 := card_autI_mul_card_inf hV hAN
    rw [hAC, Subgroup.card_bot, mul_one] at h1
    rw [h1, hA27]
  have hBc : ∀ x ∈ autI hV A, ∀ y ∈ autI hV A, x * y = y * x := by
    intro x hx y hy
    obtain ⟨g₁, hg₁, rfl⟩ := (mem_autI hV).1 hx
    obtain ⟨g₂, hg₂, rfl⟩ := (mem_autI hV).1 hy
    rw [← map_mul, ← map_mul]
    exact congrArg (convI hV) (Subtype.ext (hAc _ hg₁ _ hg₂))
  have hcj : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := fun a ha s hs =>
    (Subgroup.mem_normalizer_iff.mp (hAS ha) s).mp hs
  have hBT : autI hV A ≤
      Subgroup.normalizer ((autI hV S : Subgroup (MulAut (IntMod (W315 X) hV))) : Set _) := by
    intro φ hφ
    obtain ⟨⟨a, haN⟩, haA, rfl⟩ := (mem_autI hV).1 hφ
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      obtain ⟨⟨s, hsN⟩, hsS, rfl⟩ := (mem_autI hV).1 ht
      refine (mem_autI hV).2 ⟨⟨a, haN⟩ * ⟨s, hsN⟩ * ⟨a, haN⟩⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      simpa using hcj a haA s hsS
    · intro ht
      obtain ⟨⟨s, hsN⟩, hsS, hst⟩ := (mem_autI hV).1 ht
      refine (mem_autI hV).2 ⟨⟨a, haN⟩⁻¹ * ⟨s, hsN⟩ * ⟨a, haN⟩, ?_, ?_⟩
      · have := hcj a⁻¹ (inv_mem haA) s hsS
        simpa using this
      · rw [map_mul, map_mul, map_inv, hst]
        group
  have hFFhyp := ffHyp_W315 hK hS2 hXS hq hWL
  obtain ⟨hTL, hT4⟩ := a10_internal hFFhyp e1 (autI_mono hV (le_top : S ≤ ⊤))
    (B2F.isPGroup_autI hV hS2 hSN) (autI_mono hV hAL) hBc hB27 hBT
  have hAoffL : Aoff ≤ autI hV (oResidual 2 X) := hAoffS.trans hTL
  have hAoff4 : Nat.card Aoff ≤ 4 := (Subgroup.card_le_of_le hAoffS).trans hT4
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨hcq⟩ := nonempty_centerQuotient_equiv_of_simple hFFhyp.2.1 this e1
  have hlt := hK10 (IntMod (W315 X) hV) (fun v => IntMod.sq_eq_one v) (autI hV ⊤)
    (autI hV (oResidual 2 X)) Aoff hFFhyp ⟨hcq⟩ hAoffL hA1 hAe hAoff4
  exact absurd hAoff (not_le.mpr hlt)

end XLevel

section GLevel

theorem leaf_false_of_a10 {G : Type} [Group G] [Finite G] {Y S A : Subgroup G}
    (hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S))
    (hY : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y)
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hS2 : IsPGroup 2 S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hFF : FF153 Y S) (hno : ¬ CharNormal153 Y S)
    (φA : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
    (hAY : A ≤ Y) (hA27 : Nat.card A = 27) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA3 : ∀ x ∈ A, x ^ 3 = 1) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hK10 : A10NoV4Offender) : False := by
  obtain ⟨φ⟩ := Push153.nonempty_oResidual_quotient_equiv hS2 hSY hY3
  have hF : generalizedFitting ↥(Y ⊔ S) = CFSG.pCore 2 ↥(Y ⊔ S) :=
    Push153.generalizedFitting_sup_eq hY hS2 hSY
  have hq : CFSG.IsQuasisimple ↥(oResidual 2 (↥(Y ⊔ S) ⧸ CFSG.pCore 2 ↥(Y ⊔ S))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hYq
  have hSmap : (S.subgroupOf (Y ⊔ S)).map (Y ⊔ S).subtype = S := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right]
  have hS2' : IsPGroup 2 ↥(S.subgroupOf (Y ⊔ S)) :=
    hS2.of_injective (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)).injective
  have hS1' : S.subgroupOf (Y ⊔ S) ≠ ⊥ := by
    intro h
    apply hFF.2
    have hSb : S = ⊥ := by
      have h2 := hSmap
      rw [h, Subgroup.map_bot] at h2
      exact h2.symm
    exact (Push153.thompsonJ_le_self S).trans (hSb.le.trans bot_le)
  have hQS' : CFSG.pCore 2 ↥(Y ⊔ S) ≤ S.subgroupOf (Y ⊔ S) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hFF.1 ((Push153.mem_pCore_iff_mem_pCoreOf x).mp hx)
  have hXS : oResidual 2 ↥(Y ⊔ S) ⊔ S.subgroupOf (Y ⊔ S) = ⊤ := by
    rw [Push153.oResidual_sup_eq hS2 hSY hY3]
    have h := Subgroup.subgroupOf_sup (le_sup_left : Y ≤ Y ⊔ S) (le_sup_right : S ≤ Y ⊔ S)
    rw [Subgroup.subgroupOf_self] at h
    exact h.symm
  have hJ' : ¬ CFSG.Quasithin.thompsonJ (S.subgroupOf (Y ⊔ S)) ≤ CFSG.pCore 2 ↥(Y ⊔ S) := by
    intro h
    apply hFF.2
    have key : CFSG.Quasithin.thompsonJ ((S.subgroupOf (Y ⊔ S)).map (Y ⊔ S).subtype) =
        (CFSG.Quasithin.thompsonJ (S.subgroupOf (Y ⊔ S))).map (Y ⊔ S).subtype :=
      CFSG.Quasithin.thompsonJ_map_of_injective' (Y ⊔ S).subtype_injective _
    rw [hSmap] at key
    rw [key]
    exact Subgroup.map_mono h
  have hno' : ¬ ∃ C : Subgroup ↥(Y ⊔ S), C ≠ ⊥ ∧ C ≤ S.subgroupOf (Y ⊔ S) ∧
      (C.subgroupOf (S.subgroupOf (Y ⊔ S))).Characteristic ∧ C.Normal := by
    rintro ⟨C', hC'b, hC'S, hC'char, hC'n⟩
    apply hno
    unfold CharNormal153
    refine ⟨C'.map (Y ⊔ S).subtype, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hC'b ((Subgroup.map_eq_bot_iff_of_injective C' (Y ⊔ S).subtype_injective).mp h)
    · exact Subgroup.map_le_iff_le_comap.mpr hC'S
    · let ι : ↥(S.subgroupOf (Y ⊔ S)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)
      have hc := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.characteristic_map_equiv' ι hC'char
      have heq : (C'.subgroupOf (S.subgroupOf (Y ⊔ S))).map ι.toMonoidHom =
          (C'.map (Y ⊔ S).subtype).subgroupOf S := by
        ext x
        constructor
        · intro hx
          obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
          rw [← hyx]
          exact Subgroup.mem_subgroupOf.mpr
            (Subgroup.mem_map.mpr ⟨y.1, Subgroup.mem_subgroupOf.mp hy, rfl⟩)
        · intro hx
          obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
          have hcS : c ∈ S.subgroupOf (Y ⊔ S) := Subgroup.mem_subgroupOf.mpr (by
            have h' : (c : G) = (x : G) := hcx
            rw [h']
            exact x.2)
          exact Subgroup.mem_map.mpr ⟨⟨c, hcS⟩, Subgroup.mem_subgroupOf.mpr hc, Subtype.ext hcx⟩
      rw [heq] at hc
      exact hc
    · exact le_normalizer_map_subtype_of_normal hC'n
  have hAle : A ≤ Y ⊔ S := hAY.trans le_sup_left
  have hA27' : Nat.card (A.subgroupOf (Y ⊔ S)) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv]
    exact hA27
  have hAc' : ∀ x ∈ A.subgroupOf (Y ⊔ S), ∀ y ∈ A.subgroupOf (Y ⊔ S), x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  have hA3' : ∀ x ∈ A.subgroupOf (Y ⊔ S), x ^ 3 = 1 := by
    intro x hx
    exact Subtype.ext (hA3 _ (Subgroup.mem_subgroupOf.mp hx))
  have hAS' : A.subgroupOf (Y ⊔ S) ≤ Subgroup.normalizer
      ((S.subgroupOf (Y ⊔ S) : Subgroup ↥(Y ⊔ S)) : Set ↥(Y ⊔ S)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have h1 := Subgroup.mem_normalizer_iff.mp (hAS (Subgroup.mem_subgroupOf.mp hx)) (s : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using h1
  exact false_of_a10_pushing_up hK10 hKH hF hq hS2' hS1' hQS' hXS hJ' hno' (φ.trans φA)
    hA27' hAc' hA3' hAS'

end GLevel

section Leaf

theorem step153PushA10R_of_inputs (hK10 : A10NoV4Offender) (h149 : Sec16.Item149S14)
    (htwin : Claim153TwinR) : Step153PushA10R := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY ⟨φA⟩
  exfalso
  have hh := hR.toSec14Std
  have hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y :=
    Push153.generalizedFitting_eq_of_mem_scriptY0Star hh (h149 G A c L hh) (htwin G A c L hR) hY
  have hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y := hY.prop.1.2.1
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  have hKP : CFSG.Open.IsKProper G := hh.toTheoremFourHyp.kProper
  have hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S) :=
    hKP.isKGroup (Y ⊔ S) (sup_ne_top_of_pCoreOf_ne_bot hh.toTheoremFourHyp hSY hO2)
  have hD := hR.toSec13Data
  have hFE : CFSG.RankThree.LocalRank.partTwoF G = CFSG.RankThree.LocalRank.partTwoE G :=
    (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  have hmax : ∀ E ∈ CFSG.RankThree.LocalRank.partTwoE G, ∀ B : Subgroup G,
      CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E :=
    fun E hE B hB hEB => (hFE ▸ hE : E ∈ CFSG.RankThree.LocalRank.partTwoF G).2.1 B hB hEB
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAY : A ≤ Y := Sec16.Step163Alt.le_of_alternating_ten hmax hD.isElemAbelian hAN hO2 φA
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  exact leaf_false_of_a10 hKH hF hY3 hYq hS2 hSY hFF hno φA hAY hD.card_eq
    (fun x hx y hy => congrArg Subtype.val (hD.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hD.isElemAbelian.2 x hx) hAS hK10

end Leaf

end CFSG.RankThree.PartTwo.Sec15.F153
