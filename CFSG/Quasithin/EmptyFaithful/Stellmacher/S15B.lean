module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S15A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.H1Orth
public import CFSG.Quasithin.EmptyFaithful.SzF53MDict

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S15

variable {G : Type} [Group G]

theorem conj_eq_iff_comm {a b : G} : b * a * b⁻¹ = a ↔ a * b = b * a := by
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem exists_mem_of_h1 {X V L N : Subgroup G} [(L.subgroupOf N).Normal]
    {θ : ↥X →* Equiv.Perm (Fin 5)} {β : orth.W →* ↥N ⧸ L.subgroupOf N}
    (hθ : Function.Surjective θ) (hsd : SecData orth X L N θ β)
    (hker : ∀ x : ↥X, θ x = 1 → ∀ v ∈ V, (x : G) * v * (x : G)⁻¹ = v)
    (hVN : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ N) {v : G} (hv : v ∈ V) :
    ∃ n ∈ N, ∀ x ∈ X, x * (n⁻¹ * v) * x⁻¹ * (n⁻¹ * v)⁻¹ ∈ L := by
  set e : orth.W ≃* (↥N ⧸ L.subgroupOf N) := MulEquiv.ofBijective β ⟨hsd.inj, hsd.surj⟩
  have heβ : ∀ w, e w = β w := fun w => rfl
  let cm : ↥X → ↥N := fun x => ⟨(x : G) * v * (x : G)⁻¹ * v⁻¹, hVN x x.2 v hv⟩
  let cj : ↥X → ↥N → ↥N := fun x n => ⟨(x : G) * n * (x : G)⁻¹, hsd.conj_mem x.2 n.2⟩
  have hequiv : ∀ (x : ↥X) (n : ↥N), e.symm (QuotientGroup.mk (cj x n)) =
      orth.act (θ x) (e.symm (QuotientGroup.mk n)) := by
    intro x n
    have h1 : β (e.symm (QuotientGroup.mk n)) = QuotientGroup.mk n := by
      rw [← heβ, MulEquiv.apply_symm_apply]
    obtain ⟨hkx, h2⟩ := hsd.equiv x (e.symm (QuotientGroup.mk n)) n h1
    rw [MulEquiv.symm_apply_eq, heβ, h2]
  have hcm : ∀ x y : ↥X, θ x = θ y → cm x = cm y := by
    intro x y hxy
    have h1 : θ (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := hker _ h1 v hv
    apply Subtype.ext
    show (x : G) * v * (x : G)⁻¹ * v⁻¹ = (y : G) * v * (y : G)⁻¹ * v⁻¹
    have hx : (x : G) = (y : G) * ((y⁻¹ * x : ↥X) : G) := by simp
    rw [hx, show (y : G) * ((y⁻¹ * x : ↥X) : G) * v * ((y : G) * ((y⁻¹ * x : ↥X) : G))⁻¹ =
      (y : G) * (((y⁻¹ * x : ↥X) : G) * v * ((y⁻¹ * x : ↥X) : G)⁻¹) * (y : G)⁻¹ by group, h2]
  have hcmul : ∀ x y : ↥X, cm (x * y) = cj x (cm y) * cm x := by
    intro x y
    apply Subtype.ext
    show (x : G) * y * v * ((x : G) * y)⁻¹ * v⁻¹ =
      (x : G) * ((y : G) * v * (y : G)⁻¹ * v⁻¹) * (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹ * v⁻¹)
    group
  set ι : Equiv.Perm (Fin 5) → ↥X := Function.surjInv hθ
  have hι : ∀ σ, θ (ι σ) = σ := Function.surjInv_eq hθ
  set f : Equiv.Perm (Fin 5) → orth.W := fun σ => e.symm (QuotientGroup.mk (cm (ι σ))) with hf
  have hcoc : ∀ σ τ, f (σ * τ) = f σ * orth.act σ (f τ) := by
    intro σ τ
    have h1 : cm (ι (σ * τ)) = cm (ι σ * ι τ) := hcm _ _ (by rw [map_mul, hι, hι, hι])
    simp only [hf]
    rw [h1, hcmul, QuotientGroup.mk_mul, map_mul, hequiv, hι, mul_comm]
  obtain ⟨w, hw⟩ := h1_perm5_orth f hcoc
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (e w)
  have hnw : e.symm (QuotientGroup.mk n) = w := by rw [hn, MulEquiv.symm_apply_apply]
  refine ⟨n, n.2, fun x hx => ?_⟩
  have h1 : f (θ ⟨x, hx⟩) = e.symm (QuotientGroup.mk (cm ⟨x, hx⟩)) := by
    simp only [hf]
    rw [hcm _ _ (hι _)]
  have h2 : e.symm (QuotientGroup.mk (cm ⟨x, hx⟩)) =
      e.symm (QuotientGroup.mk (cj ⟨x, hx⟩ n * n⁻¹)) := by
    rw [← h1, hw, ← hnw, ← hequiv, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul,
      map_inv]
  have h3 := (QuotientGroup.eq (s := L.subgroupOf N)).mp (e.symm.injective h2).symm
  rw [Subgroup.mem_subgroupOf] at h3
  have h4 : (n : G)⁻¹ * (((cj ⟨x, hx⟩ n * n⁻¹)⁻¹ * cm ⟨x, hx⟩ : ↥N) : G) * (n : G)⁻¹⁻¹ ∈ L := by
    have := (inferInstance : (L.subgroupOf N).Normal).conj_mem _
      (Subgroup.mem_subgroupOf.mpr h3) n⁻¹
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have e1 : (n : G)⁻¹ * (((cj ⟨x, hx⟩ n * n⁻¹)⁻¹ * cm ⟨x, hx⟩ : ↥N) : G) * (n : G)⁻¹⁻¹ =
      x * ((n : G)⁻¹ * v) * x⁻¹ * ((n : G)⁻¹ * v)⁻¹ := by
    simp only [cj, cm, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e1] at h4
  exact h4

theorem isOrthSec_of_split {X V L N : Subgroup G} (horth : IsOrthSec X L N)
    (hLN : L ≤ N) (hNV : N ≤ V) (hVX : V ≤ X)
    (hXV : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (hVN : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ N)
    (hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ = l)
    (hcS : ∀ x ∈ cSecIn X L N, ∀ v ∈ V, x * v * x⁻¹ = v)
    (hcen : ∀ u ∈ V, (∀ x ∈ X, x * u * x⁻¹ * u⁻¹ ∈ L) → ∀ x ∈ X, x * u * x⁻¹ = u) :
    IsOrthSec X (V ⊓ Subgroup.centralizer (X : Set G)) V := by
  obtain ⟨hLNn, θ, β, hθ, hθk, hsd⟩ := horth
  set C := V ⊓ Subgroup.centralizer (X : Set G) with hCdef
  have memC : ∀ u, u ∈ C ↔ u ∈ V ∧ ∀ x ∈ X, x * u * x⁻¹ = u := by
    intro u
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine and_congr_right fun _ => forall₂_congr fun x _ => ?_
    rw [conj_eq_iff_comm, eq_comm]
  have hker : ∀ x : ↥X, θ x = 1 → ∀ v ∈ V, (x : G) * v * (x : G)⁻¹ = v := fun x hx =>
    hcS x ((mem_cSecIn_iff_of_ker hθk x.2).mp hx)
  have hdec : ∀ v ∈ V, ∃ n ∈ N, n⁻¹ * v ∈ C := by
    intro v hv
    obtain ⟨n, hn, hl⟩ := exists_mem_of_h1 hθ hsd hker hVN hv
    have hu : n⁻¹ * v ∈ V := V.mul_mem (V.inv_mem (hNV hn)) hv
    exact ⟨n, hn, (memC _).mpr ⟨hu, hcen _ hu hl⟩⟩
  have hNC : ∀ n ∈ N, n ∈ C → n ∈ L := by
    intro n hn hnC
    obtain ⟨w, hw⟩ := hsd.surj (QuotientGroup.mk ⟨n, hn⟩)
    have hfix : ∀ σ, orth.act σ w = w := by
      intro σ
      obtain ⟨x, rfl⟩ := hθ σ
      obtain ⟨hxn, h1⟩ := hsd.equiv x w ⟨n, hn⟩ hw
      apply hsd.inj
      rw [h1, hw]
      congr 1
      exact Subtype.ext (((memC n).mp hnC).2 x x.2)
    have h1 := orth_eq_one_of_fixed hfix
    rw [h1, map_one] at hw
    have := (QuotientGroup.eq_one_iff _).mp hw.symm
    exact Subgroup.mem_subgroupOf.mp this
  have hLC : L ≤ C := fun l hl => (memC l).mpr ⟨hNV (hLN hl), fun x hx => hXL x hx l hl⟩
  have hCV : C ≤ V := inf_le_left
  have hCn : (C.subgroupOf V).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCV]
    intro c v hc hv
    rw [((memC c).mp hc).2 v (hVX hv)]
    exact hc
  have hcSeq : cSecIn X C V = cSecIn X L N := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hx, hxV⟩
      refine Subgroup.subset_closure ⟨hx, fun n hn => hNC _ ?_ (hxV n (hNV hn))⟩
      exact N.mul_mem (hsd.conj_mem hx hn) (N.inv_mem hn)
    · intro x hx
      have hxX : x ∈ X := (Subgroup.closure_le X).mpr (fun _ h => h.1) hx
      refine Subgroup.subset_closure ⟨hxX, fun v hv => ?_⟩
      rw [hcS x hx v hv, mul_inv_cancel]
      exact C.one_mem
  have hι : L.subgroupOf N ≤ (C.subgroupOf V).comap (Subgroup.inclusion hNV) := fun l hl => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hLC (Subgroup.mem_subgroupOf.mp hl)
  let π : ↥N ⧸ L.subgroupOf N →* ↥V ⧸ C.subgroupOf V :=
    QuotientGroup.map _ _ (Subgroup.inclusion hNV) hι
  have hπmk : ∀ n : ↥N, π (QuotientGroup.mk n) = QuotientGroup.mk ⟨(n : G), hNV n.2⟩ :=
    fun n => rfl
  refine ⟨hCn, θ, π.comp β, hθ, by rw [hθk, hcSeq], ⟨?_, ?_, ?_⟩⟩
  · intro q
    obtain ⟨⟨v, hv⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, hnv⟩ := hdec v hv
    obtain ⟨w, hw⟩ := hsd.surj (QuotientGroup.mk ⟨n, hn⟩)
    refine ⟨w, ?_⟩
    rw [MonoidHom.comp_apply, hw, hπmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hnv
  · rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (β w)
    rw [MonoidHom.comp_apply, ← hn, hπmk, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hw
    have hnL : (n : G) ∈ L := hNC n n.2 hw
    apply hsd.inj
    rw [map_one, ← hn]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hnL)
  · intro k u x hux
    refine ⟨hXV k k.2 x x.2, ?_⟩
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (β u)
    obtain ⟨hkn, h1⟩ := hsd.equiv k u n hn.symm
    rw [MonoidHom.comp_apply, ← hn, hπmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hux
    rw [MonoidHom.comp_apply, h1, hπmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc : (n : G)⁻¹ * x ∈ C := by simpa using hux
    have e : ((k : G) * n * (k : G)⁻¹)⁻¹ * ((k : G) * x * (k : G)⁻¹) =
        (k : G) * ((n : G)⁻¹ * x) * (k : G)⁻¹ := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, ((memC _).mp hc).2 k k.2]
    exact hc

end F53.Stellmacher.S15

end CFSG.Quasithin
