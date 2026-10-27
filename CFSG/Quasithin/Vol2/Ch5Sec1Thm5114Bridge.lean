module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114SL3
public import CFSG.Quasithin.H13.StatementsL5
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4

public section

namespace CFSG.Quasithin.H13.SL3

open CFSG.Assembly.LowTwoRank Matrix

section Bridge

variable {G : Type} [Group G] {K T V : Subgroup G}

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem rho_conj (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {t : G} (ht : t ∈ T)
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    Setup.rho V T hTV ⟨t, ht⟩ * Setup.rho V K hKV k * (Setup.rho V T hTV ⟨t, ht⟩)⁻¹ =
      Setup.rho V K hKV ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp htK k).mp k.2⟩ := by
  refine MulEquiv.ext fun v => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, ← map_inv, Setup.rho_apply_coe, Setup.rho_apply_coe,
    Setup.rho_apply_coe, Setup.rho_apply_coe]
  simp only [InvMemClass.coe_inv]
  group

theorem mem_normalizer_of_conj' {H : Subgroup G} {g : G} (h₁ : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h₂ : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h₁ x, fun hx => ?_⟩
  have := h₂ _ hx
  simpa [mul_assoc] using this

variable {F : Type} [Field F]

theorem exists_maxParabolic_of_noGraph (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hS : IsSylowTwoOf (T ⊓ K) K) (π : ↥(StatedSL 3 F) →* ↥(autOn K V))
    (hπ : Function.Surjective π)
    (hker : ∀ g, π g = 1 → ∃ c : F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1)
    (hno : NoGraphAutomorphism π (autOn T V))
    (hU : ((T ⊓ K).subgroupOf K).map (InternalSec.autOnHom hKV) =
      ((unitri F).subgroupOf (StatedSL 3 F)).map π) :
    ∃ P : Subgroup G, IsMaxParabolic2 K P ∧ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) :
      Set G) ≤ P ∧ T ≤ Subgroup.normalizer (P : Set G) := by
  classical
  set φ := InternalSec.autOnHom hKV with hφdef
  have hφs := InternalSec.autOnHom_surjective hKV
  have hφv : ∀ k : ↥K, ((φ k : ↥(autOn K V)) : MulAut ↥V) = Setup.rho V K hKV k := fun _ => rfl
  set Sb := ((T ⊓ K).subgroupOf K).map φ with hSb
  set Pb := ((lineStab F).subgroupOf (StatedSL 3 F)).map π with hPb
  set P : Subgroup G := (Pb.comap φ).map K.subtype with hPdef
  have mem_P : ∀ k : ↥K, (k : G) ∈ P ↔ φ k ∈ Pb := by
    intro k
    constructor
    · rintro ⟨k', hk', hkk⟩
      have : k' = k := Subtype.ext hkk
      rw [← this]
      exact hk'
    · intro hk
      exact ⟨k, hk, rfl⟩
  have L1 : ∀ g : ↥(StatedSL 3 F), π g ∈ Pb → (g : GL (Fin 3) F) ∈ lineStab F := by
    rintro g ⟨p, hp, hpg⟩
    have h1 : π (p⁻¹ * g) = 1 := by rw [map_mul, map_inv, hpg, inv_mul_cancel]
    obtain ⟨c, hc⟩ := hker _ h1
    have hz : ((p⁻¹ * g : ↥(StatedSL 3 F)) : GL (Fin 3) F) ∈ lineStab F :=
      mem_lineStab_of_scalar hc
    have e : (g : GL (Fin 3) F) = (p : GL (Fin 3) F) * ((p⁻¹ * g : ↥(StatedSL 3 F)) :
        GL (Fin 3) F) := by simp
    rw [e]
    exact (lineStab F).mul_mem hp hz
  have hUP : ((unitri F).subgroupOf (StatedSL 3 F)).map π ≤ Pb :=
    Subgroup.map_mono fun x hx => unitri_le_lineStab hx
  have L1' : ∀ g : ↥(StatedSL 3 F), π g ∈ Sb → (g : GL (Fin 3) F) ∈ lineStab F := by
    intro g hg
    rw [hU] at hg
    exact L1 g (hUP hg)
  have hu1 : (⟨u1 F, u1_mem_statedSL⟩ : ↥(StatedSL 3 F)) ∈ (unitri F).subgroupOf (StatedSL 3 F) :=
    u1_mem_unitri
  have hu2 : (⟨u2 F, u2_mem_statedSL⟩ : ↥(StatedSL 3 F)) ∈ (unitri F).subgroupOf (StatedSL 3 F) :=
    u2_mem_unitri
  have hu1S : π ⟨u1 F, u1_mem_statedSL⟩ ∈ Sb := by
    rw [hU]; exact Subgroup.mem_map_of_mem π hu1
  have hu2S : π ⟨u2 F, u2_mem_statedSL⟩ ∈ Sb := by
    rw [hU]; exact Subgroup.mem_map_of_mem π hu2
  have L2 : ∀ y : ↥(autOn K V), (∀ s ∈ Sb, y⁻¹ * s * y ∈ Sb) → ∀ g : ↥(StatedSL 3 F),
      π g = y → (g : GL (Fin 3) F) ∈ lineStab F := by
    intro y hy g hg
    apply mem_lineStab_of_conj
    · have h1 : π (g⁻¹ * ⟨u1 F, u1_mem_statedSL⟩ * g) ∈ Sb := by
        rw [map_mul, map_mul, map_inv, hg]
        exact hy _ hu1S
      simpa using L1' _ h1
    · have h1 : π (g⁻¹ * ⟨u2 F, u2_mem_statedSL⟩ * g) ∈ Sb := by
        rw [map_mul, map_mul, map_inv, hg]
        exact hy _ hu2S
      simpa using L1' _ h1
  have hB : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ P := by
    rintro x ⟨hxK, hxN⟩
    rw [show x = ((⟨x, hxK⟩ : ↥K) : G) from rfl, mem_P]
    obtain ⟨g, hg⟩ := hπ (φ ⟨x, hxK⟩)
    have hnorm : ∀ s ∈ Sb, (φ ⟨x, hxK⟩)⁻¹ * s * φ ⟨x, hxK⟩ ∈ Sb := by
      rintro _ ⟨s₀, hs₀, rfl⟩
      refine ⟨⟨x, hxK⟩⁻¹ * s₀ * ⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr ?_,
        by rw [map_mul, map_mul, map_inv]⟩
      have hs₀' : (s₀ : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hs₀
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp hs₀'
      simpa using this
    exact ⟨g, L2 _ hnorm g hg, hg⟩
  have key : ∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P := by
    intro t ht x hx
    obtain ⟨⟨x, hxK⟩, hxP, rfl⟩ := hx
    have htK := hTK ht
    set tb := Setup.rho V T hTV ⟨t, ht⟩ with htb
    have htbT : tb ∈ autOn T V := (Setup.mem_autOn_self_iff hTV).2 ⟨⟨t, ht⟩, rfl⟩
    obtain ⟨A, σ, hA⟩ := hno tb htbT
    have htS : ∀ s : ↥(autOn K V), s ∈ Sb → ∀ h : tb * (s : MulAut ↥V) * tb⁻¹ ∈ autOn K V,
        (⟨_, h⟩ : ↥(autOn K V)) ∈ Sb := by
      rintro _ ⟨s₀, hs₀, rfl⟩ h
      have hs₀' : (s₀ : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hs₀
      have hts : t * s₀ * t⁻¹ ∈ T ⊓ K :=
        ⟨T.mul_mem (T.mul_mem ht hs₀'.1) (T.inv_mem ht),
          (Subgroup.mem_normalizer_iff.mp htK _).mp hs₀'.2⟩
      refine ⟨⟨t * s₀ * t⁻¹, hts.2⟩, Subgroup.mem_subgroupOf.mpr hts, ?_⟩
      apply Subtype.ext
      rw [hφv]
      exact (rho_conj hKV hTV ht htK s₀).symm
    have hdet : ∀ g : GL (Fin 3) F, g ∈ StatedSL 3 F →
        A * Matrix.GeneralLinearGroup.map σ.toRingHom g * A⁻¹ ∈ StatedSL 3 F := by
      intro g hg
      rw [mem_statedSL]
      have h1 := mem_statedSL.mp (map_mem_statedSL σ hg)
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h1, mul_one,
        ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have hAu : ∀ (u : GL (Fin 3) F) (hu : u ∈ StatedSL 3 F),
        Matrix.GeneralLinearGroup.map σ.toRingHom u = u → π ⟨u, hu⟩ ∈ Sb →
          (A⁻¹)⁻¹ * u * A⁻¹ ∈ lineStab F := by
      intro u hu hσu huS
      have h1 := hA ⟨u, hu⟩ (hdet u hu)
      have hmemt : tb * ((π ⟨u, hu⟩ : ↥(autOn K V)) : MulAut ↥V) * tb⁻¹ ∈ autOn K V := by
        rw [← h1]
        exact (π ⟨_, hdet u hu⟩).2
      have h2 : π ⟨_, hdet u hu⟩ ∈ Sb := by
        have h3 := htS (π ⟨u, hu⟩) huS hmemt
        have e : (⟨_, hmemt⟩ : ↥(autOn K V)) = π ⟨_, hdet u hu⟩ := Subtype.ext h1.symm
        rw [e] at h3
        exact h3
      have h4 := L1' _ h2
      simp only [hσu] at h4
      simpa using h4
    have hA1 : A ∈ lineStab F := by
      have hinv : A⁻¹ ∈ lineStab F :=
        mem_lineStab_of_conj (hAu _ u1_mem_statedSL (map_u1 σ) hu1S)
          (hAu _ u2_mem_statedSL (map_u2 σ) hu2S)
      simpa using (lineStab F).inv_mem hinv
    obtain ⟨p, hp, hpx⟩ := hxP
    have hxt : t * x * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htK x).mp hxK
    show ((⟨t * x * t⁻¹, hxt⟩ : ↥K) : G) ∈ P
    rw [mem_P]
    refine ⟨⟨_, hdet p p.2⟩, ?_, ?_⟩
    · exact (lineStab F).mul_mem ((lineStab F).mul_mem hA1 (map_mem_lineStab σ hp))
        ((lineStab F).inv_mem hA1)
    · apply Subtype.ext
      rw [hA p (hdet p p.2), hpx, hφv, hφv]
      exact rho_conj hKV hTV ht htK ⟨x, hxK⟩
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
    mem_normalizer_of_conj' (key t ht) fun x hx => by
      have := key t⁻¹ (T.inv_mem ht) x hx
      simpa using this
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hne : P ≠ K := by
    intro hPK'
    obtain ⟨k, hk⟩ := hφs (π ⟨wSL F, wSL_mem_statedSL⟩)
    have hkP : (k : G) ∈ P := by rw [hPK']; exact k.2
    rw [mem_P, hk] at hkP
    exact wSL_notMem_lineStab (L1 _ hkP)
  have hmax : ∀ Q : Subgroup G, IsParabolic2 K Q → Q ≠ K → P ≤ Q → Q = P := by
    intro Q hQ hQK hPQ
    by_contra hne'
    have hQP : ¬ Q ≤ P := fun h => hne' (le_antisymm h hPQ)
    obtain ⟨q, hqQ, hqP⟩ := Set.not_subset.mp hQP
    have hqK : q ∈ K := hQ.1 hqQ
    obtain ⟨g₀, hg₀⟩ := hπ (φ ⟨q, hqK⟩)
    have hg₀P : (g₀ : GL (Fin 3) F) ∉ lineStab F := by
      intro h
      apply hqP
      show ((⟨q, hqK⟩ : ↥K) : G) ∈ P
      rw [mem_P, ← hg₀]
      exact ⟨g₀, h, rfl⟩
    set H : Subgroup (GL (Fin 3) F) :=
      (((Q.subgroupOf K).map φ).comap π).map (StatedSL 3 F).subtype with hH
    have hHS : H ≤ StatedSL 3 F := Subgroup.map_subtype_le _
    have hPH : StatedSL 3 F ⊓ lineStab F ≤ H := by
      rintro g ⟨hgS, hgL⟩
      obtain ⟨k, hk⟩ := hφs (π ⟨g, hgS⟩)
      have hkP : (k : G) ∈ P := by
        rw [mem_P, hk]
        exact ⟨⟨g, hgS⟩, hgL, rfl⟩
      exact ⟨⟨g, hgS⟩, ⟨k, Subgroup.mem_subgroupOf.mpr (hPQ hkP), hk⟩, rfl⟩
    have hg₀H : (g₀ : GL (Fin 3) F) ∈ H :=
      ⟨g₀, ⟨⟨q, hqK⟩, Subgroup.mem_subgroupOf.mpr hqQ, hg₀.symm⟩, rfl⟩
    have hSLH := statedSL_le_of_lineStab_lt hHS hPH hg₀H hg₀P
    apply hQK
    refine le_antisymm hQ.1 fun k hk => ?_
    obtain ⟨g, hg⟩ := hπ (φ ⟨k, hk⟩)
    obtain ⟨g', hg'Q, hg'eq⟩ := hSLH g.2
    have hgg : g' = g := Subtype.ext hg'eq
    obtain ⟨q', hq'Q, hq'eq⟩ := hg'Q
    have hker' : φ (q'⁻¹ * ⟨k, hk⟩) = 1 := by
      rw [map_mul, map_inv, hq'eq, hgg, hg, inv_mul_cancel]
    have hP1 : ((q'⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ P := by
      rw [mem_P, hker']
      exact Pb.one_mem
    have e : k = (q' : G) * ((q'⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [e]
    exact Q.mul_mem (Subgroup.mem_subgroupOf.mp hq'Q) (hPQ hP1)
  exact ⟨P, ⟨⟨hPK, T ⊓ K, hS, hB⟩, hne, hmax⟩, hB, hTP⟩

theorem not_isDiagramNontrivial_of_noGraph [Finite G] [Finite F] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ m) (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hS : IsSylowTwoOf (T ⊓ K) K) (π : ↥(StatedSL 3 F) →* ↥(autOn K V))
    (hπ : Function.Surjective π)
    (hker : ∀ g, π g = 1 → ∃ c : F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1)
    (hno : NoGraphAutomorphism π (autOn T V)) : ¬ E2.IsDiagramNontrivial T K (T ⊓ K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := InternalSec.autOnHom hKV with hφdef
  set Sb : Sylow 2 ↥(autOn K V) :=
    (A4.toSylow hS).mapSurjective (InternalSec.autOnHom_surjective hKV) with hSbdef
  set Ub : Sylow 2 ↥(autOn K V) := (unitriSylow hm hF).mapSurjective hπ with hUbdef
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (↥(autOn K V)) Ub Sb
  obtain ⟨g₀, hg₀⟩ := hπ y
  set π' : ↥(StatedSL 3 F) →* ↥(autOn K V) := π.comp (MulAut.conj g₀).toMonoidHom with hπ'
  have hπ'v : ∀ h, π' h = π (g₀ * h * g₀⁻¹) := fun h => rfl
  have hπ's : Function.Surjective π' := by
    intro z
    obtain ⟨h, hh⟩ := hπ z
    exact ⟨g₀⁻¹ * h * g₀, by rw [hπ'v]; simpa [mul_assoc] using hh⟩
  have hker' : ∀ g, π' g = 1 →
      ∃ c : F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1 := by
    intro g hg
    obtain ⟨c, hc⟩ := hker _ ((hπ'v g).symm.trans hg)
    refine ⟨c, ?_⟩
    have e : (g : GL (Fin 3) F) = ((g₀ : GL (Fin 3) F))⁻¹ *
        ((g₀ * g * g₀⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) * (g₀ : GL (Fin 3) F) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact conj_scalar hc
  have hU : ((T ⊓ K).subgroupOf K).map φ = ((unitri F).subgroupOf (StatedSL 3 F)).map π' := by
    ext x
    have h1 : x ∈ ((T ⊓ K).subgroupOf K).map φ ↔ x ∈ (Sb : Subgroup ↥(autOn K V)) := Iff.rfl
    rw [h1, ← hy, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
    constructor
    · rintro ⟨u, hu, hux⟩
      refine ⟨u, hu, ?_⟩
      rw [hπ'v, map_mul, map_mul, map_inv, hux, hg₀]
      group
    · rintro ⟨u, hu, hux⟩
      refine ⟨u, hu, ?_⟩
      rw [hπ'v, map_mul, map_mul, map_inv, hg₀] at hux
      rw [← hux]
      group
  have hno' : NoGraphAutomorphism π' (autOn T V) := by
    intro t ht
    obtain ⟨A, σ, hA⟩ := hno t ht
    refine ⟨((g₀ : GL (Fin 3) F))⁻¹ * A *
      Matrix.GeneralLinearGroup.map σ.toRingHom (g₀ : GL (Fin 3) F), σ, fun g h => ?_⟩
    have hmem : A * Matrix.GeneralLinearGroup.map σ.toRingHom
        ((g₀ * g * g₀⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) * A⁻¹ ∈ StatedSL 3 F := by
      rw [mem_statedSL]
      have h1 := mem_statedSL.mp (map_mem_statedSL σ (g₀ * g * g₀⁻¹).2)
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h1, mul_one,
        ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have e : (MulAut.conj g₀) ⟨_, h⟩ = (⟨_, hmem⟩ : ↥(StatedSL 3 F)) := by
      apply Subtype.ext
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      group
    show ((π ((MulAut.conj g₀) ⟨_, h⟩) : ↥(autOn K V)) : MulAut ↥V) = _
    rw [e, hA _ hmem]
    rfl
  obtain ⟨P, hP, hB, hTP⟩ :=
    exists_maxParabolic_of_noGraph hKV hTV hTK hS π' hπ's hker' hno' hU
  exact fun hd => hd P hP hB hTP

end Bridge

end CFSG.Quasithin.H13.SL3
