module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.PermNormal

public section

namespace CFSG.Quasithin.F53.Stellmacher
open Equiv CFSG.Open CFSG.LieType.BorelTits
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

theorem index_two_facts {G : Type} [Group G] {N Q : Subgroup G}
    (h : N.relIndex Q = 2) :
    (∀ x ∈ Q, x * x ∈ N) ∧ (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ N) := by
  set N' : Subgroup ↥Q := N.subgroupOf Q with hN'
  have hi : N'.index = 2 := h
  have : N'.Normal := Subgroup.normal_of_index_eq_two hi
  have hcard : Nat.card (↥Q ⧸ N') = 2 := hi
  have hsq : ∀ a : ↥Q ⧸ N', a * a = 1 := by
    intro a
    rw [← pow_two]
    have := pow_card_eq_one' (G := ↥Q ⧸ N') (x := a)
    rwa [hcard] at this
  have hmem : ∀ z : ↥Q, (QuotientGroup.mk z : ↥Q ⧸ N') = 1 → (z : G) ∈ N := fun z hz =>
    (QuotientGroup.eq_one_iff z).mp hz
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · exact hmem ⟨x * x, Q.mul_mem hx hx⟩ (hsq (QuotientGroup.mk ⟨x, hx⟩))
  · refine hmem ⟨x * y * x⁻¹ * y⁻¹, Q.mul_mem (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem hx)) (Q.inv_mem hy)⟩ ?_
    have hx' : (QuotientGroup.mk ⟨x, hx⟩ : ↥Q ⧸ N')⁻¹ = QuotientGroup.mk ⟨x, hx⟩ :=
      inv_eq_of_mul_eq_one_right (hsq _)
    have hy' : (QuotientGroup.mk ⟨y, hy⟩ : ↥Q ⧸ N')⁻¹ = QuotientGroup.mk ⟨y, hy⟩ :=
      inv_eq_of_mul_eq_one_right (hsq _)
    have e : (QuotientGroup.mk ⟨x * y * x⁻¹ * y⁻¹, Q.mul_mem (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem hx)) (Q.inv_mem hy)⟩ : ↥Q ⧸ N') =
        (QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨y, hy⟩ * (QuotientGroup.mk ⟨x, hx⟩)⁻¹ * (QuotientGroup.mk ⟨y, hy⟩)⁻¹ : ↥Q ⧸ N') := rfl
    rw [e, hx', hy']
    have h2 := hsq (QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨y, hy⟩)
    simpa [mul_assoc] using h2

theorem perm5_pow_eight : ∀ σ : Perm (Fin 5), σ ^ 8 = 1 → Perm.sign σ = 1 → σ ^ 2 = 1 := by
  decide +kernel

theorem exists_central_alt (D Zb : Subgroup (Perm (Fin 5))) (hD : Nat.card D = 8) (hZD : Zb ≤ D)
    (hZn : ∀ d ∈ D, ∀ z ∈ Zb, d * z * d⁻¹ ∈ Zb) (hZ1 : Zb ≠ ⊥) :
    ∃ z ∈ Zb, z ≠ 1 ∧ z ∈ alternatingGroup (Fin 5) ∧ z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hD]; norm_num)
  have : Group.IsNilpotent D := hp.isNilpotent
  set H : Subgroup D := Zb.subgroupOf D with hH
  have : H.Normal := ⟨fun n hn g => by
    rw [hH, Subgroup.mem_subgroupOf] at hn ⊢
    exact hZn g.1 g.2 _ hn⟩
  have hH1 : H ≠ ⊥ := by
    intro h
    apply hZ1
    rw [eq_bot_iff]
    intro z hz
    have : (⟨z, hZD hz⟩ : D) ∈ H := Subgroup.mem_subgroupOf.mpr hz
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  obtain ⟨⟨w, hw⟩, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
  obtain ⟨z, hzD⟩ := w
  have hzH : z ∈ Zb := (Subgroup.mem_subgroupOf.mp ((Subgroup.mem_inf.mp hw).1))
  have hzc : ∀ y ∈ D, y * z = z * y := by
    intro y hy
    have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hz1 : z ≠ 1 := by
    intro h; exact hwne (Subtype.ext (Subtype.ext h))
  have hA := sign_eq_one_of_central_card_eight D hD z hzD hzc
  refine ⟨z, hzH, hz1, hA, perm5_pow_eight z ?_ (Equiv.Perm.mem_alternatingGroup.mp hA)⟩
  have := pow_card_eq_one' (G := D) (x := ⟨z, hzD⟩)
  rw [hD] at this
  simpa using congrArg Subtype.val this

theorem not_pgroup_of_cyc (Pm : Subgroup (Perm (Fin 5))) (h : (swap (0 : Fin 5) 1 * swap 1 2) ∈ Pm) : ¬ IsPGroup 2 Pm := by
  intro hp
  have h3 : orderOf (swap (0 : Fin 5) 1 * swap 1 2) = 3 := orderOf_eq_prime (p := 3)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨_, h⟩
  rw [Subgroup.orderOf_mk, h3] at hk
  rcases k with _ | _ | k
  · simp at hk
  · simp at hk
  · have : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
    omega

theorem module_lemma (hM6 : NoA5Transvection) {G : Type} [Group G] [Finite G]
    (B Q F N : Subgroup G) (ψ : ↥B →* Perm (Fin 5)) (hsurj : Function.Surjective ψ)
    (hker : ∀ x : ↥B, ψ x = 1 ↔ (x : G) ∈ Q) (hQB : Q ≤ B)
    (hFN : F ≤ N) (hNQ : N ≤ Q) (hidx : N.relIndex Q = 2)
    (hFnorm : ∀ g ∈ B, ∀ f ∈ F, g * f * g⁻¹ ∈ F)
    (hsq : ∀ x ∈ Q, x * x ∈ F) (hcm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ F)
    (s : ↥B) (hs1 : ψ s ≠ 1) (hs2 : ψ s ^ 2 = 1) (hsA : ψ s ∈ alternatingGroup (Fin 5))
    (hsN : ∀ n ∈ N, (s : G) * n * (s : G)⁻¹ * n⁻¹ ∈ F) :
    ∀ a : ↥B, ψ a ∈ alternatingGroup (Fin 5) → ∀ q ∈ Q, (a : G) * q * (a : G)⁻¹ * q⁻¹ ∈ F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F' : Subgroup ↥B := F.subgroupOf B with hF'
  have hF'n : F'.Normal := ⟨fun n hn g => by
    rw [hF', Subgroup.mem_subgroupOf] at hn ⊢
    exact hFnorm g.1 g.2 _ hn⟩
  have hFQ : F ≤ Q := hFN.trans hNQ
  let π : ↥B →* ↥B ⧸ F' := QuotientGroup.mk' F'
  have hFker : F' ≤ ψ.ker := fun x hx => (hker x).mpr (hFQ hx)
  let ψh : (↥B ⧸ F') →* Perm (Fin 5) := QuotientGroup.lift F' ψ hFker
  have hψh : ∀ b : ↥B, ψh (π b) = ψ b := fun b => rfl
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective F'
  have hsurjh : Function.Surjective ψh := fun σ => by
    obtain ⟨b, rfl⟩ := hsurj σ; exact ⟨π b, rfl⟩
  set V : Subgroup (↥B ⧸ F') := ψh.ker with hV
  have hVmem : ∀ v ∈ V, ∃ q : ↥B, (q : G) ∈ Q ∧ π q = v := by
    intro v hv
    obtain ⟨b, rfl⟩ := hπ v
    exact ⟨b, (hker b).mp hv, rfl⟩
  have hQV : ∀ q : ↥B, (q : G) ∈ Q → π q ∈ V := fun q hq => by
    rw [hV, MonoidHom.mem_ker, hψh]; exact (hker q).mpr hq
  have hπ1 : ∀ x : ↥B, π x = 1 ↔ (x : G) ∈ F := fun x => QuotientGroup.eq_one_iff x
  have hπcomm : ∀ x y : ↥B, (x : G) ∈ Q → (y : G) ∈ Q → π x * π y = π y * π x := by
    intro x y hx hy
    have h := (hπ1 (x * y * x⁻¹ * y⁻¹)).mpr (hcm _ hx _ hy)
    simp only [map_mul, map_inv] at h
    calc π x * π y = (π x * π y * (π x)⁻¹ * (π y)⁻¹) * (π y * π x) := by group
      _ = π y * π x := by rw [h, one_mul]
  have hπsq : ∀ x : ↥B, (x : G) ∈ Q → π x * π x = 1 := by
    intro x hx
    have h := (hπ1 (x * x)).mpr (hsq _ hx)
    simpa using h
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    obtain ⟨x, hx, rfl⟩ := hVmem v hv
    obtain ⟨y, hy, rfl⟩ := hVmem w hw
    exact hπcomm x y hx hy
  have hVsq : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hVmem v hv
    exact hπsq x hx
  have hVn : V.Normal := MonoidHom.normal_ker ψh
  have hVp : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by simpa [pow_two] using hVsq v.1 v.2)⟩
  have hVab : IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hVcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]; exact hVsq x hx
  have hVtop : (⊤ : Subgroup (↥B ⧸ F')) ≤ Subgroup.normalizer (V : Set (↥B ⧸ F')) :=
    (Subgroup.normalizer_eq_top_iff.mpr hVn).ge
  have hcore : pCoreOf 2 (⊤ : Subgroup (↥B ⧸ F')) = V := by
    refine le_antisymm ?_ ?_
    · set P := pCoreOf 2 (⊤ : Subgroup (↥B ⧸ F')) with hP
      have hP2 : IsPGroup 2 P := pCoreOf_isPGroup 2 _
      have hPn : P.Normal :=
        Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 2 ⊤))
      have hPmn : (P.map ψh).Normal := hPn.map ψh hsurjh
      have hPm2 : IsPGroup 2 (P.map ψh) := hP2.map ψh
      rcases normal_perm_five _ hPmn with h | h | h
      · intro p hp
        have : ψh p ∈ P.map ψh := ⟨p, hp, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact this
      · exact absurd hPm2 (not_pgroup_of_cyc _ (by
          rw [h, Equiv.Perm.mem_alternatingGroup]; decide +kernel))
      · exact absurd hPm2 (not_pgroup_of_cyc _ (by rw [h]; trivial))
    · exact le_pCoreOf_of_le_normalizer 2 le_top hVtop hVp
  let ψ'' : ↥(⊤ : Subgroup (↥B ⧸ F')) →* Perm (Fin 5) := ψh.comp (⊤ : Subgroup (↥B ⧸ F')).subtype
  have hsurj'' : Function.Surjective ψ'' := fun σ => by
    obtain ⟨x, rfl⟩ := hsurjh σ; exact ⟨⟨x, trivial⟩, rfl⟩
  have hker'' : ∀ x : ↥(⊤ : Subgroup (↥B ⧸ F')), ψ'' x = 1 ↔
      (x : ↥B ⧸ F') ∈ pCoreOf 2 (⊤ : Subgroup (↥B ⧸ F')) := by
    intro x; rw [hcore]; exact Iff.rfl
  set C : Subgroup (↥B ⧸ F') := Subgroup.centralizer (V : Set (↥B ⧸ F')) with hC
  have hCn : C.Normal := ⟨fun c hc g => by
    rw [hC, Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ V := hVn.conj_mem v hv g⁻¹
    rw [inv_inv] at hv'
    have h := hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * v := by group⟩
  have hKn : (C.map ψh).Normal := hCn.map ψh hsurjh
  have hVC : V ≤ C := fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw => hVcomm w hw v hv
  set Nbar : Subgroup (↥B ⧸ F') := (N.subgroupOf B).map π with hNbar
  have hNbarV : Nbar ≤ V := by
    rintro _ ⟨n, hn, rfl⟩
    exact hQV n (hNQ (Subgroup.mem_subgroupOf.mp hn))
  have hNbarC : Nbar ≤ Subgroup.centralizer ({π s} : Set (↥B ⧸ F')) := by
    rintro _ ⟨n, hn, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := (hπ1 (s * n * s⁻¹ * n⁻¹)).mpr (hsN _ (Subgroup.mem_subgroupOf.mp hn))
    simp only [map_mul, map_inv] at h1
    calc π s * π n = (π s * π n * (π s)⁻¹ * (π n)⁻¹) * (π n * π s) := by group
      _ = π n * π s := by rw [h1, one_mul]
  have hVeq : V = (Q.subgroupOf B).map π := by
    ext v
    constructor
    · intro hv
      obtain ⟨q, hq, rfl⟩ := hVmem v hv
      exact ⟨q, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact hQV q (Subgroup.mem_subgroupOf.mp hq)
  have hrel : Nbar.relIndex V = 2 := by
    have hk : π.ker = F' := QuotientGroup.ker_mk' F'
    have hF'N : F' ≤ N.subgroupOf B := fun x hx => hFN hx
    have hN'Q : N.subgroupOf B ≤ Q.subgroupOf B := fun x hx => hNQ hx
    rw [hNbar, hVeq, Subgroup.relIndex_map_map, hk, sup_eq_left.mpr hF'N,
      sup_eq_left.mpr (hF'N.trans hN'Q), Subgroup.relIndex_subgroupOf hQB]
    exact hidx
  have hAK : alternatingGroup (Fin 5) ≤ C.map ψh := by
    by_contra hnot
    have hKbot : C.map ψh = ⊥ := by
      rcases normal_perm_five _ hKn with h | h | h
      · exact h
      · exact absurd h.ge hnot
      · exact absurd (h ▸ le_top) hnot
    have hCV : C ≤ V := fun c hc => by
      have : ψh c ∈ C.map ψh := ⟨c, hc, rfl⟩
      rw [hKbot, Subgroup.mem_bot] at this
      exact this
    have hM := hM6 (↥B ⧸ F') ⊤ V ψ'' hsurj'' hker'' hcore.ge hVtop hVab
      (by rw [hcore, top_inf_eq]; exact le_antisymm hCV hVC) (π s) trivial hs1 hs2 hsA
    have hdvd : (V ⊓ Subgroup.centralizer ({π s} : Set (↥B ⧸ F'))).relIndex V ∣ 2 := by
      rw [← hrel]
      exact Subgroup.relIndex_dvd_of_le_left V (le_inf hNbarV hNbarC)
    have h1 : (V ⊓ Subgroup.centralizer ({π s} : Set (↥B ⧸ F'))).relIndex V = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exact absurd h hM
    have hVle : V ≤ V ⊓ Subgroup.centralizer ({π s} : Set (↥B ⧸ F')) :=
      Subgroup.relIndex_eq_one.mp h1
    have hsC : π s ∈ C := Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hVle hv).2 (π s) rfl).symm
    have : ψh (π s) ∈ C.map ψh := ⟨_, hsC, rfl⟩
    rw [hKbot, Subgroup.mem_bot] at this
    exact hs1 this
  intro a ha q hq
  have hqB : q ∈ B := hQB hq
  obtain ⟨c, hc, hcψ⟩ := hAK ha
  have hd : c⁻¹ * π a ∈ V := by
    rw [hV, MonoidHom.mem_ker, map_mul, map_inv, hcψ]
    exact inv_mul_cancel _
  have hv : π ⟨q, hqB⟩ ∈ V := hQV _ hq
  have hcom : π a * π ⟨q, hqB⟩ = π ⟨q, hqB⟩ * π a := by
    have e1 : π a = c * (c⁻¹ * π a) := by group
    have e2 := hVcomm _ hd _ hv
    have e3 := Subgroup.mem_centralizer_iff.mp hc _ hv
    calc π a * π ⟨q, hqB⟩ = c * ((c⁻¹ * π a) * π ⟨q, hqB⟩) := by group
      _ = c * (π ⟨q, hqB⟩ * (c⁻¹ * π a)) := by rw [e2]
      _ = (c * π ⟨q, hqB⟩) * (c⁻¹ * π a) := by group
      _ = (π ⟨q, hqB⟩ * c) * (c⁻¹ * π a) := by rw [e3]
      _ = π ⟨q, hqB⟩ * π a := by group
  have h1 : π (a * ⟨q, hqB⟩ * a⁻¹ * ⟨q, hqB⟩⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcom]; group
  exact (hπ1 _).mp h1

theorem lemmaP (hM6 : NoA5Transvection) :
    ∀ (G : Type) [Group G] [Finite G] (B Q S Z : Subgroup G) (ψ : ↥B →* Equiv.Perm (Fin 5))
      (Ω : Type) (N : Ω → Subgroup G) (α : Ω),
      Function.Surjective ψ → (∀ x : ↥B, ψ x = 1 ↔ (x : G) ∈ Q) →
      Q ≤ S → S ≤ B → Z ≤ S → (∀ μ, N μ ≤ Q) → (∀ μ, (N μ).relIndex Q = 2) →
      (∀ μ ν, ∃ g ∈ B, N ν = (N μ).map (MulAut.conj g).toMonoidHom) →
      (∀ g ∈ B, ∀ μ, ∃ ν, N ν = (N μ).map (MulAut.conj g).toMonoidHom) →
      Nat.card ((S.subgroupOf B).map ψ) = 8 →
      S ≤ Subgroup.normalizer (N α : Set G) →
      ¬ Z ≤ Q →
      (∀ s ∈ S, ∀ z ∈ Z, ∃ z' ∈ Z, ∃ q ∈ Q, s * z * s⁻¹ = z' * q) →
      ⁅N α, Z⁆ ≤ ⨅ μ, N μ →
      ∀ μ, N μ = N α := by
  intro G _ _ B Q S Z ψ Ω N α hsurj hker hQS hSB hZS hNQ hidx htrans hclos hS8 hSN hZQ hZn hcomm μ
  classical
  have hQB : Q ≤ B := hQS.trans hSB
  have hZB : Z ≤ B := hZS.trans hSB
  set F : Subgroup G := ⨅ μ, N μ with hF
  have hFN : ∀ μ, F ≤ N μ := fun μ => iInf_le _ μ
  have hmemF : ∀ x, x ∈ F ↔ ∀ μ, x ∈ N μ := fun x => by rw [hF, Subgroup.mem_iInf]
  have hFnorm : ∀ g ∈ B, ∀ f ∈ F, g * f * g⁻¹ ∈ F := by
    intro g hg f hf
    rw [hmemF] at hf ⊢
    intro μ
    obtain ⟨ν, hν⟩ := hclos g⁻¹ (B.inv_mem hg) μ
    have hfν : f ∈ N ν := hf ν
    rw [hν] at hfν
    obtain ⟨y, hy, hyf⟩ := hfν
    have : g * f * g⁻¹ = y := by
      rw [← hyf]; simp; group
    rw [this]; exact hy
  have hsqF : ∀ x ∈ Q, x * x ∈ F := fun x hx =>
    (hmemF _).mpr fun μ => (index_two_facts (hidx μ)).1 x hx
  have hcmF : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ F := fun x hx y hy =>
    (hmemF _).mpr fun μ => (index_two_facts (hidx μ)).2 x hx y hy
  set D : Subgroup (Perm (Fin 5)) := (S.subgroupOf B).map ψ with hD
  set Zb : Subgroup (Perm (Fin 5)) := (Z.subgroupOf B).map ψ with hZb
  have hZbD : Zb ≤ D := Subgroup.map_mono (fun x hx => hZS hx)
  have hZbn : ∀ d ∈ D, ∀ z ∈ Zb, d * z * d⁻¹ ∈ Zb := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨z, hz, rfl⟩
    obtain ⟨z', hz', q, hq, he⟩ := hZn (s : G) hs (z : G) hz
    have hz'B : z' ∈ B := hZB hz'
    have hqB : q ∈ B := hQB hq
    refine ⟨⟨z', hz'B⟩, hz', ?_⟩
    have h1 : (s * z * s⁻¹ : ↥B) = ⟨z', hz'B⟩ * ⟨q, hqB⟩ := Subtype.ext he
    have h2 := congrArg ψ h1
    rw [map_mul, map_mul, map_mul, map_inv, (hker ⟨q, hqB⟩).mpr hq, mul_one] at h2
    exact h2.symm
  have hZb1 : Zb ≠ ⊥ := by
    intro h
    obtain ⟨z, hz, hzQ'⟩ := Set.not_subset.mp hZQ
    have hzB : z ∈ B := hZB hz
    have : ψ ⟨z, hzB⟩ ∈ Zb := ⟨⟨z, hzB⟩, hz, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hzQ' ((hker ⟨z, hzB⟩).mp this)
  obtain ⟨zb, hzb, hzb1, hzbA, hzb2⟩ := exists_central_alt D Zb hS8 hZbD hZbn hZb1
  obtain ⟨x, hxZ, rfl⟩ := hzb
  have hxZ' : (x : G) ∈ Z := hxZ
  have hxN : ∀ n ∈ N α, (x : G) * n * (x : G)⁻¹ * n⁻¹ ∈ F := by
    intro n hn
    have h1 := Subgroup.commutator_mem_commutator hn hxZ'
    have h2 : n * (x : G) * n⁻¹ * (x : G)⁻¹ ∈ F := hcomm h1
    have : (x : G) * n * (x : G)⁻¹ * n⁻¹ = (n * (x : G) * n⁻¹ * (x : G)⁻¹)⁻¹ := by group
    rw [this]; exact F.inv_mem h2
  have key := module_lemma hM6 B Q F (N α) ψ hsurj hker hQB (hFN α) (hNQ α) (hidx α) hFnorm
    hsqF hcmF x hzb1 hzb2 hzbA hxN
  have hDA : ¬ D ≤ alternatingGroup (Fin 5) := by
    intro h
    have := Subgroup.card_dvd_of_le h
    rw [hS8, card_alt5] at this
    omega
  obtain ⟨d, hd, hdA⟩ := Set.not_subset.mp hDA
  obtain ⟨s0, hs0, rfl⟩ := hd
  have hs0S : (s0 : G) ∈ S := hs0
  have hA : ∀ a : ↥B, ψ a ∈ alternatingGroup (Fin 5) → ∀ n ∈ N α, (a : G) * n * (a : G)⁻¹ ∈ N α := by
    intro a ha n hn
    have := key a ha n (hNQ α hn)
    have h2 : (a : G) * n * (a : G)⁻¹ = ((a : G) * n * (a : G)⁻¹ * n⁻¹) * n := by group
    rw [h2]; exact (N α).mul_mem (hFN α this) hn
  have hnormB : ∀ g : ↥B, ∀ n ∈ N α, (g : G) * n * (g : G)⁻¹ ∈ N α := by
    intro g n hn
    by_cases hg : ψ g ∈ alternatingGroup (Fin 5)
    · exact hA g hg n hn
    · have haA : ψ (g * s0⁻¹) ∈ alternatingGroup (Fin 5) := by
        have hdA' : ψ s0 ∉ alternatingGroup (Fin 5) := hdA
        rw [Equiv.Perm.mem_alternatingGroup] at hg hdA' ⊢
        rw [map_mul, map_inv, Perm.sign_mul, Perm.sign_inv]
        rcases Int.units_eq_one_or (Perm.sign (ψ g)) with h | h
        · exact absurd h hg
        · rcases Int.units_eq_one_or (Perm.sign (ψ s0)) with h' | h'
          · exact absurd h' hdA'
          · rw [h, h']; decide
      have hn' : (s0 : G) * n * (s0 : G)⁻¹ ∈ N α :=
        (Subgroup.mem_normalizer_iff.mp (hSN hs0S) n).mp hn
      have := hA _ haA _ hn'
      have e : ((g * s0⁻¹ : ↥B) : G) * ((s0 : G) * n * (s0 : G)⁻¹) * ((g * s0⁻¹ : ↥B) : G)⁻¹ =
          (g : G) * n * (g : G)⁻¹ := by
        simp [mul_assoc]
      rw [e] at this
      exact this
  obtain ⟨g, hgB, hg⟩ := htrans α μ
  have hle : N μ ≤ N α := by
    rw [hg]
    rintro _ ⟨n, hn, rfl⟩
    exact hnormB ⟨g, hgB⟩ n hn
  have hcard : Nat.card (N μ) = Nat.card (N α) := by
    rw [hg]; exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact Subgroup.eq_of_le_of_card_ge hle (hcard ▸ le_rfl)

end CFSG.Quasithin.F53.Stellmacher
