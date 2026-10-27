module

public import CFSG.Quasithin.EmptyFaithful.SzN32Frat

public section

open scoped commutatorElement

namespace CFSG.Quasithin.SzN32

namespace Base

section Identities

variable {G : Type*} [Group G]

theorem cm_pow_three (x s : G) :
    cm (x ^ 3) s = (x⁻¹ * x⁻¹ * cm x s * x * x) * (x⁻¹ * cm x s * x) * cm x s := by
  unfold cm
  simp only [pow_succ, pow_zero, one_mul]
  group

theorem cm_mul_left (g h w : G) : cm (g * h) w = h⁻¹ * cm g w * h * cm h w := by
  unfold cm
  group

theorem cm_eq_commutatorElement (g h : G) : cm g h = ⁅g⁻¹, h⁻¹⁆ := by
  simp [cm, commutatorElement_def]

theorem cm_eq_one_iff {g h : G} : cm g h = 1 ↔ Commute g h := by
  rw [cm_eq_commutatorElement, commutatorElement_eq_one_iff_commute, Commute.inv_inv_iff]

theorem cm_mem_commutator (g h : G) : cm g h ∈ commutator G := by
  rw [cm_eq_commutatorElement]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem cm_cm_eq_one {K : Subgroup G} (hK : K ≤ Subgroup.center G) (w : G)
    (hw : ∀ g, cm g w ∈ K) (x s : G) : cm (cm x s) w = 1 := by
  have hc : ∀ g h : G, h * cm g w = cm g w * h :=
    fun g h => Subgroup.mem_center_iff.1 (hK (hw g)) h
  let ψ : G →* G := MonoidHom.mk' (fun g => cm g w) (fun g h => by
    show cm (g * h) w = cm g w * cm h w
    rw [cm_mul_left, hc g h⁻¹, inv_mul_cancel_right])
  have h1 : cm (cm x w) (cm s w) = 1 := cm_eq_one_iff.2 (hc s (cm x w))
  exact (map_cm ψ x s).trans h1

theorem central_shuffle {ζ : G} (h : ∀ g : G, ζ * g = g * ζ) (v : G) :
    v * ζ * ζ * (v * ζ) * v = v ^ 3 * ζ ^ 3 := by
  have hrc : ∀ a : G, a * ζ * v = a * v * ζ := fun a => by rw [mul_assoc, h v, ← mul_assoc]
  simp only [← mul_assoc]
  simp only [hrc]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem cube_eq_one {K : Subgroup G} (hK : K ≤ Subgroup.center G) (hK3 : ∀ k ∈ K, k ^ 3 = 1)
    (x s v : G) (hv : cm x s = v) (hx : x ^ 3 ∈ K) (hζ : cm v x ∈ K) : v ^ 3 = 1 := by
  have hζc : ∀ g : G, cm v x * g = g * cm v x :=
    fun g => (Subgroup.mem_center_iff.1 (hK hζ) g).symm
  have h1 : x⁻¹ * v * x = v * cm v x := by
    unfold cm
    group
  have h2 : x⁻¹ * x⁻¹ * v * x * x = v * cm v x * cm v x := by
    have h3 : x⁻¹ * cm v x * x = cm v x := by
      rw [mul_assoc, hζc x, inv_mul_cancel_left]
    calc x⁻¹ * x⁻¹ * v * x * x = x⁻¹ * (x⁻¹ * v * x) * x := by group
      _ = x⁻¹ * (v * cm v x) * x := by rw [h1]
      _ = (x⁻¹ * v * x) * (x⁻¹ * cm v x * x) := by group
      _ = v * cm v x * cm v x := by rw [h1, h3]
  have h3 : cm (x ^ 3) s = 1 := cm_eq_one_iff.2 (Subgroup.mem_center_iff.1 (hK hx) s).symm
  rw [cm_pow_three, hv, h2, h1, central_shuffle hζc v, hK3 _ hζ, mul_one] at h3
  exact h3

theorem cube_eq_one_of_commute (v s w : G) (hw : cm v s = w) (hv : v ^ 3 = 1)
    (hvw : cm v w = 1) : w ^ 3 = 1 := by
  have h1 : cm (v ^ 3) s = 1 := by
    rw [hv]
    unfold cm
    group
  rw [cm_pow_three, hw] at h1
  have hc : v * w = w * v := cm_eq_one_iff.1 hvw
  have e1 : v⁻¹ * w * v = w := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have e2 : v⁻¹ * v⁻¹ * w * v * v = w := by
    calc v⁻¹ * v⁻¹ * w * v * v = v⁻¹ * (v⁻¹ * w * v) * v := by group
      _ = w := by rw [e1, e1]
  rw [e2, e1] at h1
  calc w ^ 3 = w * w * w := by simp only [pow_succ, pow_zero, one_mul]
    _ = 1 := h1

theorem ker_pow_three {K : Subgroup G} (hK : Nat.card K = 3) : ∀ k ∈ K, k ^ 3 = 1 := by
  intro k hk
  have h := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
  rw [hK] at h
  simpa using congrArg Subtype.val h

end Identities

theorem ker_le_center {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G) {K : Subgroup G}
    [K.Normal] (hK : Nat.card K = 3) : K ≤ Subgroup.center G := by
  have hne : K ≠ ⊥ := by
    rintro rfl
    simp at hK
  obtain ⟨Z, hZK, hZc, hZ3⟩ := exists_central_card_three hG hne
  have hZ : Z = K := Subgroup.eq_of_le_of_card_ge hZK (by rw [hK, hZ3])
  exact hZ ▸ hZc

theorem z_mem_center {S : Type*} [Group S] {a σ : S} (hT : TData a σ) :
    cm (cm a σ) σ ∈ Subgroup.center S := by
  have h : Subgroup.closure ({a, σ} : Set S) ≤ Subgroup.centralizer {cm (cm a σ) σ} := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact hT.z_comm_a
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact hT.z_comm_σ
  rw [hT.gen] at h
  rw [Subgroup.mem_center_iff]
  intro g
  have := h (Subgroup.mem_top g)
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this _ rfl).symm

theorem conj_mem_closure {S : Type*} [Group S] {s : Set S} (g : S)
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) {n : S} (hn : n ∈ Subgroup.closure s) :
    g * n * g⁻¹ ∈ Subgroup.closure s := by
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem normal_closure_pair {S : Type*} [Group S] [Finite S] {a σ : S} (hT : TData a σ) :
    (Subgroup.closure ({cm a σ, cm (cm a σ) σ} : Set S)).Normal := by
  set C := Subgroup.closure ({cm a σ, cm (cm a σ) σ} : Set S) with hC
  have hu : cm a σ ∈ C := Subgroup.subset_closure (by simp)
  have hz : cm (cm a σ) σ ∈ C := Subgroup.subset_closure (by simp)
  have ha : a ∈ Subgroup.normalizer (C : Set S) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    refine conj_mem_closure a ?_ hn
    rintro x (rfl | rfl)
    · rw [← hT.u_comm_a]
      simpa using hu
    · rw [← hT.z_comm_a]
      simpa using hz
  have hσ : σ⁻¹ ∈ Subgroup.normalizer (C : Set S) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    refine conj_mem_closure σ⁻¹ ?_ hn
    rintro x (rfl | rfl)
    · have : σ⁻¹ * cm a σ * σ⁻¹⁻¹ = cm a σ * cm (cm a σ) σ := by
        unfold cm
        group
      rw [this]
      exact mul_mem hu hz
    · have : σ⁻¹ * cm (cm a σ) σ * σ⁻¹⁻¹ = cm (cm a σ) σ := by
        rw [inv_inv, mul_assoc, hT.z_comm_σ, inv_mul_cancel_left]
      rw [this]
      exact hz
  have hle : Subgroup.closure ({a, σ} : Set S) ≤ Subgroup.normalizer (C : Set S) := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ha
    · simpa using inv_mem hσ
  rw [hT.gen] at hle
  exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hle)

theorem card_closure_pair {S : Type*} [Group S] {u z : S} (hz : z ∈ Subgroup.center S)
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hu3 : u ^ 3 = 1) (hu : u ∉ Subgroup.zpowers z) :
    Nat.card (Subgroup.closure ({u, z} : Set S)) = 9 := by
  have hu1 : u ≠ 1 := fun h => hu (h ▸ Subgroup.one_mem _)
  have hA : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz3 hz1
  have hB : Nat.card (Subgroup.zpowers u) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hu3 hu1
  have hAn : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hz)
  have hclos : Subgroup.closure ({u, z} : Set S) = Subgroup.zpowers u ⊔ Subgroup.zpowers z := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.insert_eq]
  have hinf : Nat.card (Subgroup.zpowers z ⊓ Subgroup.zpowers u : Subgroup S) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers z ⊓ Subgroup.zpowers u : Subgroup S) ∣ 3 :=
      hB ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact h
    · exfalso
      have : Finite (Subgroup.zpowers u) := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
      have heq : Subgroup.zpowers z ⊓ Subgroup.zpowers u = Subgroup.zpowers u :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hB])
      have hmem : u ∈ Subgroup.zpowers z ⊓ Subgroup.zpowers u :=
        heq.symm ▸ Subgroup.mem_zpowers u
      exact hu (Subgroup.mem_inf.1 hmem).1
  have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers z) (Subgroup.zpowers u)
  have h2 := Subgroup.relIndex_mul_card (Subgroup.zpowers z)
    (Subgroup.zpowers u ⊔ Subgroup.zpowers z)
  rw [Subgroup.relIndex_sup_right, inf_eq_left.2 le_sup_right, hA] at h2
  rw [hinf, mul_one] at h1
  rw [hclos, ← h2, h1, hB]

section Preimage

variable {S : Type*} [Group S] {G : Type*} [Group G] (π : G →* S) {u z : S} {v w : G}

theorem map_closure_sup_ker (hv : π v = u) (hw : π w = z) :
    (Subgroup.closure ({v, w} : Set G) ⊔ π.ker).map π = Subgroup.closure ({u, z} : Set S) := by
  rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair, hv, hw,
    (Subgroup.map_eq_bot_iff π.ker).2 le_rfl, sup_bot_eq]

theorem normal_closure_sup_ker (hv : π v = u) (hw : π w = z)
    (hC : (Subgroup.closure ({u, z} : Set S)).Normal) :
    (Subgroup.closure ({v, w} : Set G) ⊔ π.ker).Normal := by
  have h : Subgroup.closure ({v, w} : Set G) ⊔ π.ker =
      (Subgroup.closure ({u, z} : Set S)).comap π := by
    rw [← map_closure_sup_ker π hv hw]
    exact (Subgroup.comap_map_eq_self le_sup_right).symm
  rw [h]
  exact hC.comap π

theorem isE27_closure_sup_ker (hKc : π.ker ≤ Subgroup.center G) (hK : Nat.card π.ker = 3)
    (hv : π v = u) (hw : π w = z) (hvw : v * w = w * v) (hv3 : v ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hC9 : Nat.card (Subgroup.closure ({u, z} : Set S)) = 9) :
    IsE27 (Subgroup.closure ({v, w} : Set G) ⊔ π.ker) := by
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = Subgroup.closure ({v, w} : Set G) ⊔ π.ker := ⟨_, rfl⟩
  rw [← hE]
  have hmap : E.map π = Subgroup.closure ({u, z} : Set S) := by
    rw [hE]
    exact map_closure_sup_ker π hv hw
  have hKE : π.ker ≤ E := hE ▸ le_sup_right
  have hE' : E = Subgroup.closure ({v, w} ∪ (π.ker : Set G)) := by
    rw [hE, Subgroup.closure_union, Subgroup.closure_eq]
  have hpw : ({v, w} ∪ (π.ker : Set G)).Pairwise Commute := by
    have hvw' : Commute v w := hvw
    have hpair : ∀ p q : G, p ∈ ({v, w} : Set G) → q ∈ ({v, w} : Set G) → Commute p q := by
      rintro p q (rfl | rfl) (rfl | rfl)
      · exact Commute.refl _
      · exact hvw'
      · exact hvw'.symm
      · exact Commute.refl _
    intro x hx y hy _
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact hpair x y hx hy
      · exact Subgroup.mem_center_iff.1 (hKc hy) x
    · exact (Subgroup.mem_center_iff.1 (hKc hx) y).symm
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    have := Subgroup.isMulCommutative_closure hpw
    intro x hx y hy
    rw [hE'] at hx hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Subgroup.closure _) ⟨y, hy⟩)
  refine ⟨?_, ?_, hcomm⟩
  · have h1 := Subgroup.relIndex_mul_card π.ker E
    rw [Subgroup.relIndex_ker, hmap, inf_eq_left.2 hKE, hK, hC9] at h1
    omega
  · intro x hx
    rw [hE'] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with (hx | hx) | hx
      · rw [hx]
        exact hv3
      · rw [hx]
        exact hw3
      · exact ker_pow_three hK x hx
    | one => exact one_pow 3
    | mul x y hx hy hx3 hy3 =>
      have hc : Commute x y := hcomm x (hE' ▸ hx) y (hE' ▸ hy)
      rw [hc.mul_pow, hx3, hy3, one_mul]
    | inv x _ hx3 => rw [inv_pow, hx3, inv_one]

end Preimage

end Base

theorem base {S : Type*} [Group S] {a σ : S} (hT : TData a σ) {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 3 G) (π : G →* S) (hπ : Function.Surjective π) (hker : π.ker ≤ frattini G)
    (hK : Nat.card π.ker = 3) :
    ∃ E : Subgroup G, E.Normal ∧ E ≤ frattini G ∧ IsE27 E := by
  have : Finite S := Finite.of_surjective π hπ
  have hzc : cm (cm a σ) σ ∈ Subgroup.center S := Base.z_mem_center hT
  have hKc : π.ker ≤ Subgroup.center G := Base.ker_le_center hG hK
  have hK3 : ∀ k ∈ π.ker, k ^ 3 = 1 := Base.ker_pow_three hK
  obtain ⟨x, hx⟩ := hπ a
  obtain ⟨s, hs⟩ := hπ σ
  obtain ⟨v, hv⟩ : ∃ v, cm x s = v := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, cm v s = w := ⟨_, rfl⟩
  have hπv : π v = cm a σ := by rw [← hv, map_cm, hx, hs]
  have hπw : π w = cm (cm a σ) σ := by rw [← hw, map_cm, hπv, hs]
  have hker_cm : ∀ g h : G, Commute (π g) (π h) → cm g h ∈ π.ker := fun g h hgh => by
    rw [MonoidHom.mem_ker, map_cm]
    exact Base.cm_eq_one_iff.2 hgh
  have hR1 : cm v w = 1 := by
    have := Base.cm_cm_eq_one hKc w (fun g => hker_cm g w (by
      rw [hπw]
      exact Subgroup.mem_center_iff.1 hzc (π g))) x s
    rwa [hv] at this
  have hx3 : x ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx]
    exact hT.a_cube
  have hζ : cm v x ∈ π.ker := hker_cm v x (by
    rw [hπv, hx]
    exact hT.u_comm_a)
  have hv3 : v ^ 3 = 1 := Base.cube_eq_one hKc hK3 x s v hv hx3 hζ
  have hw3 : w ^ 3 = 1 := Base.cube_eq_one_of_commute v s w hw hv3 hR1
  have hC9 : Nat.card (Subgroup.closure ({cm a σ, cm (cm a σ) σ} : Set S)) = 9 :=
    Base.card_closure_pair hzc hT.z_ne_one hT.z_cube hT.u_cube hT.u_not_mem
  refine ⟨Subgroup.closure ({v, w} : Set G) ⊔ π.ker, ?_, ?_, ?_⟩
  · exact Base.normal_closure_sup_ker π hπv hπw (Base.normal_closure_pair hT)
  · refine sup_le ((Subgroup.closure_le _).2 ?_) hker
    intro g hg
    rcases hg with hg | hg
    · rw [hg, ← hv]
      exact commutator_le_frattini hG (Base.cm_mem_commutator x s)
    · rw [Set.mem_singleton_iff.1 hg, ← hw]
      exact commutator_le_frattini hG (Base.cm_mem_commutator v s)
  · exact Base.isE27_closure_sup_ker π hKc hK hπv hπw (Base.cm_eq_one_iff.1 hR1).eq hv3 hw3 hC9

end CFSG.Quasithin.SzN32
