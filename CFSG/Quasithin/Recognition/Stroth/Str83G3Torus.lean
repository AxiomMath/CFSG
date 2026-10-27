module

public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefModBot
public import CFSG.RankThree.GF2n.Tim81.Sec2.NaturalFixedPointwise
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.CGT.PushingUpLit.BHS6.NestedLinear
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedLemma11

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.RankThree.GF2n.Tim81.Sec2
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem l2_chiefStep_fixedLine_card {H Y S : Subgroup G} {n : ℕ}
    (hn : n ≠ 0)
    (hS : IsSylowTwoOf S H) (hYH : Y ≤ H) (hV : IsElemAbelian 2 Y)
    (hstep : IsChiefStep H Y ⊥ Y) :
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
    letI _cg : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
    ∀ (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 n))
      (ρ : Representation (ZMod 2) SL(2, GaloisField 2 n)
        (Additive (Ch3z.chiefMod ⊥ Y)))
      (φ : Additive (Ch3z.chiefMod ⊥ Y) ≃+ (Fin 2 → GaloisField 2 n)),
      (∀ (h : ↥H) (w : Ch3z.chiefMod ⊥ Y),
        ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
          Additive.ofMul (l2ChiefSectionAction hstep hE h w)) →
      (∀ g w, φ (ρ g w) =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (φ w)) →
      Nat.card ↥(Y ⊓ Subgroup.centralizer (S : Set G)) = 2 ^ n := by
  classical
  let F := GaloisField 2 n
  haveI : Fintype F := Fintype.ofFinite _
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n hn
  let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
  letI : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
  intro hE₀ e ρ φ hcompat hφnat
  have hρeq : ρ = l2ChiefSectionRep hstep hYH hE e := by
    refine MonoidHom.ext fun g' => LinearMap.ext fun w => ?_
    obtain ⟨h, rfl⟩ := e.surjective g'
    obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H) h
    have hw : Additive.ofMul w.toMul = w := rfl
    rw [← hw, QuotientGroup.mk'_apply, hcompat h' w.toMul, l2ChiefSectionRep_apply_mk]
  obtain ⟨hSH, hSp, hSidx⟩ := hS
  let q : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
  let ψ : ↥H →* SL(2, F) := e.toMonoidHom.comp q
  let A : Subgroup SL(2, F) := (S.subgroupOf H).map ψ
  have hmap : ((S.subgroupOf H).map q).map e.toMonoidHom = A := by
    rw [Subgroup.map_map]
  let PH : Sylow 2 ↥H := (hSp.comap_subtype (K := H)).toSylow hSidx
  have hPHcoe : (PH : Subgroup ↥H) = S.subgroupOf H := IsPGroup.toSylow_coe _ _
  let Pq : Sylow 2 (oTwoQuot ↥H) :=
    PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hPqcoe : (Pq : Subgroup (oTwoQuot ↥H)) = (S.subgroupOf H).map q := by
    change ((PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _) :
      Sylow 2 (oTwoQuot ↥H)) : Subgroup (oTwoQuot ↥H)) = (S.subgroupOf H).map q
    rw [Sylow.coe_mapSurjective, hPHcoe]
  let PA : Sylow 2 (SL(2, F)) :=
    Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective)
  have hPAcoe : (PA : Subgroup (SL(2, F))) = A := by
    change ((Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective) :
      Sylow 2 (SL(2, F))) : Subgroup (SL(2, F))) = A
    rw [Sylow.coe_mapSurjective, hPqcoe, hmap]
  obtain ⟨x, hx⟩ := sylow_conj_description (p := 2) PA
  have hx' : ∀ a, a ∈ A ↔ x⁻¹ * a * x ∈ upperRootGroup F := by
    intro a
    rw [← hPAcoe]
    exact hx a
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht⟩ := (mem_upperRootGroup_iff (g := x⁻¹ * a * x)).mp ((hx' a).mp ha)
    have haeq : a = x * uElt t * x⁻¹ := by
      have h := congrArg (fun z => x * z * x⁻¹) ht
      simpa [mul_assoc] using h
    rw [haeq]
    have huu : uElt t * uElt t = 1 := by
      rw [← uElt_add, CharTwo.add_self_eq_zero, uElt_zero]
    calc (x * uElt t * x⁻¹) * (x * uElt t * x⁻¹)
        = x * (uElt t * uElt t) * x⁻¹ := by group
      _ = 1 := by rw [huu]; group
  have hAeq : A = (upperRootGroup F).map (MulAut.conj x).toMonoidHom := by
    ext a
    rw [Subgroup.mem_map]
    constructor
    · intro ha
      refine ⟨x⁻¹ * a * x, (hx' a).mp ha, ?_⟩
      change (MulAut.conj x) (x⁻¹ * a * x) = a
      rw [MulAut.conj_apply]
      group
    · rintro ⟨u, hu, rfl⟩
      refine (hx' (x * u * x⁻¹)).mpr ?_
      have h : x⁻¹ * (x * u * x⁻¹) * x = u := by group
      rw [h]
      exact hu
  have hAcard : Nat.card A = Nat.card F := by
    rw [hAeq, Subgroup.card_map_of_injective (MulAut.conj x).injective,
      natCard_upperRootGroup, Nat.card_eq_fintype_card]
  have hfixcard : Nat.card (CFSG.RankThree.FFModules.fixSub ρ A) = Nat.card F :=
    IsNaturalModule.natCard_fixedSub (ρ := ρ) ⟨φ, hφnat⟩ hA2 hAcard
  have hcard : Nat.card ↥(Y ⊓ Subgroup.centralizer (S : Set G)) =
      Nat.card (CFSG.RankThree.FFModules.fixSub ρ A) := by
    have h := fixSub_chiefMod_bot_card (H := H) (U := Y) (W := Y) (m := n) hstep hYH hE e
      (S.subgroupOf H)
    rw [Subgroup.map_subgroupOf_eq_of_le hSH] at h
    rw [hmap, ← hρeq] at h
    exact h.symm
  rw [hcard, hfixcard, hFcard]

theorem inf_centralizer_le_omegaOneCenterOf_of_le {Y S : Subgroup G}
    (hYS : Y ≤ S) (hV : IsElemAbelian 2 Y) :
    Y ⊓ Subgroup.centralizer (S : Set G) ≤ omegaOneCenterOf S := by
  intro w hw
  obtain ⟨hwY, hwC⟩ := Subgroup.mem_inf.mp hw
  have hwS : w ∈ S := hYS hwY
  have hw2 : w ^ 2 = 1 := hV.2 w hwY
  have hwZ : w ∈ centerOf S := Subgroup.mem_inf.mpr ⟨hwS, hwC⟩
  exact Subgroup.subset_closure
    (show w ∈ {x : G | x ∈ centerOf S ∧ x ^ 2 = 1} from ⟨hwZ, hw2⟩)

theorem l2_chiefStep_torus_faithful {H Y S : Subgroup G} {n : ℕ}
    (hn : n ≠ 0)
    (hS : IsSylowTwoOf S H) (hYH : Y ≤ H) (hV : IsElemAbelian 2 Y)
    (hstep : IsChiefStep H Y ⊥ Y) :
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
    letI _cg : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
    ∀ (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 n))
      (ρ : Representation (ZMod 2) SL(2, GaloisField 2 n)
        (Additive (Ch3z.chiefMod ⊥ Y)))
      (φ : Additive (Ch3z.chiefMod ⊥ Y) ≃+ (Fin 2 → GaloisField 2 n)),
      (∀ (h : ↥H) (w : Ch3z.chiefMod ⊥ Y),
        ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
          Additive.ofMul (l2ChiefSectionAction hstep hE h w)) →
      (∀ g w, φ (ρ g w) =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (φ w)) →
      ∀ d ∈ H, d ∈ Subgroup.normalizer (S : Set G) → Odd (orderOf d) →
        d ∈ Subgroup.centralizer
          ((Y ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) →
        d = 1 := by
  classical
  let F := GaloisField 2 n
  haveI : Fintype F := Fintype.ofFinite _
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n hn
  let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
  letI : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
  intro hE₀ e ρ φ hcompat hφnat d hdH hdN hodd hcent
  have hρeq : ρ = l2ChiefSectionRep hstep hYH hE e := by
    refine MonoidHom.ext fun g' => LinearMap.ext fun w => ?_
    obtain ⟨h, rfl⟩ := e.surjective g'
    obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H) h
    have hw : Additive.ofMul w.toMul = w := rfl
    rw [← hw, QuotientGroup.mk'_apply, hcompat h' w.toMul, l2ChiefSectionRep_apply_mk]
  obtain ⟨hSH, hSp, hSidx⟩ := hS
  let q : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
  let ψ : ↥H →* SL(2, F) := e.toMonoidHom.comp q
  let A : Subgroup SL(2, F) := (S.subgroupOf H).map ψ
  have hmap : ((S.subgroupOf H).map q).map e.toMonoidHom = A := by
    rw [Subgroup.map_map]
  let PH : Sylow 2 ↥H := (hSp.comap_subtype (K := H)).toSylow hSidx
  have hPHcoe : (PH : Subgroup ↥H) = S.subgroupOf H := IsPGroup.toSylow_coe _ _
  let Pq : Sylow 2 (oTwoQuot ↥H) :=
    PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hPqcoe : (Pq : Subgroup (oTwoQuot ↥H)) = (S.subgroupOf H).map q := by
    change ((PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _) :
      Sylow 2 (oTwoQuot ↥H)) : Subgroup (oTwoQuot ↥H)) = (S.subgroupOf H).map q
    rw [Sylow.coe_mapSurjective, hPHcoe]
  let PA : Sylow 2 (SL(2, F)) :=
    Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective)
  have hPAcoe : (PA : Subgroup (SL(2, F))) = A := by
    change ((Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective) :
      Sylow 2 (SL(2, F))) : Subgroup (SL(2, F))) = A
    rw [Sylow.coe_mapSurjective, hPqcoe, hmap]
  obtain ⟨x, hx⟩ := sylow_conj_description (p := 2) PA
  have hx' : ∀ a, a ∈ A ↔ x⁻¹ * a * x ∈ upperRootGroup F := by
    intro a
    rw [← hPAcoe]
    exact hx a
  let dH : ↥H := ⟨d, hdH⟩
  let g : SL(2, F) := e (q dH)
  have hdHnorm : dH ∈ Subgroup.normalizer ((S.subgroupOf H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp hdN (x : G)).mp hx
    · intro hx
      have hx' : (dH * x * dH⁻¹ : ↥H) ∈ S.subgroupOf H := hx
      rw [Subgroup.mem_subgroupOf] at hx' ⊢
      have h2 : (dH : G)⁻¹ * ((dH : G) * (x : G) * (dH : G)⁻¹) * (dH : G) ∈ S := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN)
          (((dH * x * dH⁻¹ : ↥H) : G))).mp hx'
        simpa using h
      have h3 : (dH : G)⁻¹ * ((dH : G) * (x : G) * (dH : G)⁻¹) * (dH : G) =
          (x : G) := by group
      rwa [h3] at h2
  have hgA : g ∈ Subgroup.normalizer (A : Set (SL(2, F))) := by
    have hle := Subgroup.le_normalizer_map (f := ψ) (H := S.subgroupOf H)
    have hmem : ψ dH ∈ (Subgroup.normalizer ((S.subgroupOf H) : Set ↥H)).map ψ :=
      Subgroup.mem_map_of_mem ψ hdHnorm
    exact hle hmem
  let ℓ : Subgroup G := Y ⊓ Subgroup.centralizer (S : Set G)
  have hcardℓ : Nat.card ↥ℓ = 2 ^ n :=
    l2_chiefStep_fixedLine_card (n := n) hn ⟨hSH, hSp, hSidx⟩ hYH hV hstep e ρ φ
      hcompat hφnat
  have hmemfix : ∀ w : ↥ℓ,
      Additive.ofMul (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩) ∈
        CFSG.RankThree.FFModules.fixSub ρ A := by
    intro w
    rw [← hmap, hρeq]
    refine (mem_fixSub_chiefMod_bot_iff hstep hYH hE e (S.subgroupOf H)
      ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩).mpr ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hSH]
    exact (Subgroup.mem_inf.mp w.2).2
  have hmemfixd : ∀ w : ↥ℓ,
      ρ g (Additive.ofMul (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩)) =
        Additive.ofMul (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩) := by
    intro w
    have hzp : Additive.ofMul (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩) ∈
        CFSG.RankThree.FFModules.fixSub ρ
          (((Subgroup.zpowers dH).map q).map e.toMonoidHom) := by
      rw [hρeq]
      refine (mem_fixSub_chiefMod_bot_iff hstep hYH hE e (Subgroup.zpowers dH)
        ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩).mpr ?_
      rw [MonoidHom.map_zpowers]
      have hdw : d * w.1 = w.1 * d :=
        (Subgroup.mem_centralizer_iff.mp hcent w.1 w.2).symm
      have hle : Subgroup.zpowers d ≤ Subgroup.centralizer ({w.1} : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hdw)
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    have hgmem : g ∈ ((Subgroup.zpowers dH).map q).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom
        (Subgroup.mem_map_of_mem q (Subgroup.mem_zpowers dH))
    exact (CFSG.RankThree.FFModules.mem_fixSub.mp hzp) g hgmem
  have hmemroot : ∀ w : ↥ℓ,
      φ (Additive.ofMul (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩)) ∈
        rootLine x := by
    intro w
    refine mem_rootLine_of_fixed x _ (fun u hu => ?_)
    have huA : u ∈ A := (hx' u).mpr hu
    have hfixu := (CFSG.RankThree.FFModules.mem_fixSub.mp (hmemfix w)) u huA
    have hnat := hφnat u
      (Additive.ofMul (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩))
    rw [hfixu] at hnat
    rw [smul_eq_mulVec']
    exact hnat.symm
  let Φ : ↥ℓ → ↥(rootLine x) := fun w =>
    ⟨φ (Additive.ofMul (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩)),
      hmemroot w⟩
  have hinj : Function.Injective Φ := by
    intro w₁ w₂ h
    have hv : φ (Additive.ofMul
        (chiefModBotMulEquiv Y ⟨w₁.1, (Subgroup.mem_inf.mp w₁.2).1⟩)) =
        φ (Additive.ofMul
          (chiefModBotMulEquiv Y ⟨w₂.1, (Subgroup.mem_inf.mp w₂.2).1⟩)) :=
      congrArg Subtype.val h
    have h1 : Additive.ofMul
          (chiefModBotMulEquiv Y ⟨w₁.1, (Subgroup.mem_inf.mp w₁.2).1⟩) =
        Additive.ofMul
          (chiefModBotMulEquiv Y ⟨w₂.1, (Subgroup.mem_inf.mp w₂.2).1⟩) :=
      φ.injective hv
    have h2 : (⟨w₁.1, (Subgroup.mem_inf.mp w₁.2).1⟩ : ↥Y) =
        ⟨w₂.1, (Subgroup.mem_inf.mp w₂.2).1⟩ :=
      (chiefModBotMulEquiv Y).injective (by simpa using congrArg Additive.toMul h1)
    have h3 : w₁.1 = w₂.1 := congrArg (fun z : ↥Y => (z : G)) h2
    exact Subtype.ext h3
  have hrootcard : Nat.card ↥(rootLine x) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_rootLine, pow_one, hFcard]
  have hcardℓroot : Nat.card ↥ℓ = Nat.card ↥(rootLine x) := by
    rw [hcardℓ, hrootcard]
  have hbij : Function.Bijective Φ :=
    (Nat.bijective_iff_injective_and_card Φ).mpr ⟨hinj, hcardℓroot⟩
  have hsurj : Function.Surjective Φ := hbij.2
  have hgfix : ∀ v ∈ rootLine x, g • v = v := by
    intro v hv
    obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
    have hwv : φ (Additive.ofMul
        (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩)) = v :=
      congrArg Subtype.val hw
    rw [← hwv, smul_eq_mulVec']
    have hnat := hφnat g
      (Additive.ofMul (chiefModBotMulEquiv Y ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩))
    rw [hmemfixd w] at hnat
    exact hnat.symm
  have hyfix : (x⁻¹ * g * x) • (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1 := by
    have hxe : x • (Pi.single 0 1 : Fin 2 → F) ∈ rootLine x := smul_single_mem_rootLine x
    have hgx : g • (x • (Pi.single 0 1 : Fin 2 → F)) =
        x • (Pi.single 0 1 : Fin 2 → F) := hgfix _ hxe
    calc (x⁻¹ * g * x) • (Pi.single 0 1 : Fin 2 → F)
        = x⁻¹ • (g • (x • (Pi.single 0 1 : Fin 2 → F))) := by
          rw [mul_smul, mul_smul]
      _ = x⁻¹ • (x • (Pi.single 0 1 : Fin 2 → F)) := by rw [hgx]
      _ = Pi.single 0 1 := by rw [inv_smul_smul]
  have hoddg : Odd (orderOf g) := by
    have hdvd : orderOf g ∣ orderOf d := by
      have h := orderOf_map_dvd ψ dH
      have h1 : orderOf (ψ dH) = orderOf g := rfl
      rw [h1] at h
      have h2 : orderOf dH = orderOf d := by
        simpa [dH] using (Subgroup.orderOf_coe dH).symm
      rwa [h2] at h
    exact Odd.of_dvd_nat hodd hdvd
  have hordY : orderOf (x⁻¹ * g * x) = orderOf g := by
    rw [← MulAut.conj_symm_apply x g]
    exact (MulAut.conj x).symm.orderOf_eq g
  have hy1 : x⁻¹ * g * x = 1 :=
    CFSG.CGT.PushingUpLit.BHS6.eq_one_of_odd_of_smul_eq (g := x⁻¹ * g * x)
      (v := (Pi.single 0 1 : Fin 2 → F)) (by rw [hordY]; exact hoddg) (by simp) hyfix
  have hg1 : g = 1 := by
    have h := congrArg (fun z : SL(2, F) => x * z * x⁻¹) hy1
    simpa [mul_assoc] using h
  have hq1 : q dH = 1 := e.injective (by simpa [g] using hg1)
  have hq1' : (dH : ↥H ⧸ CFSG.Open.pCore 2 ↥H) = 1 := by
    simpa [q, QuotientGroup.mk'_apply] using hq1
  have hdmemH : dH ∈ CFSG.Open.pCore 2 ↥H := (QuotientGroup.eq_one_iff dH).mp hq1'
  have hdmem : d ∈ pCoreOf 2 H := Subgroup.mem_map.mpr ⟨dH, hdmemH, rfl⟩
  have hp2 : IsPGroup 2 (pCoreOf 2 H) :=
    IsPGroup.map (pCore_isPGroup (G := ↥H) (p := 2)) (Subgroup.subtype H)
  obtain ⟨k, hk⟩ := hp2.exists_orderOf_eq_pow ⟨d, hdmem⟩
  have hk' : orderOf d = 2 ^ k := by
    simpa using hk
  have hoddk : Odd (2 ^ k) := hk' ▸ hodd
  have hk0 : 2 ^ k = 1 := by
    rcases k with _ | m
    · rfl
    · exact absurd (dvd_pow_self 2 (Nat.succ_ne_zero m)) hoddk.not_two_dvd_nat
  exact orderOf_eq_one_iff.mp (hk'.trans hk0)

end CFSG.Quasithin.Stroth
