module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.DegBlocks
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.DegSplit

public section

open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Deg

universe u v

def Claim (n : ℕ) : Prop :=
  ∀ (G : Type u) (Q : Type v) [Group G] [Finite G] [Group Q] [Finite Q] (π : G →* Q),
    Function.Surjective π → Group.IsSolvable π.ker → IsSS Q →
    ∀ (Ω : Type) [Finite Ω] (f : G →* Equiv.Perm Ω), f.ker ≤ π.ker → Nat.card Ω = n →
      permDeg Q ≤ n

section Cases

variable {G : Type u} {Q : Type v} [Group G] [Group Q]

theorem ker_subgroupMap (π : G →* Q) (H : Subgroup G) :
    (π.subgroupMap H).ker = π.ker.subgroupOf H := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem ker_subgroupComap (π : G →* Q) (C : Subgroup Q) :
    (π.subgroupComap C).ker = π.ker.subgroupOf (C.comap π) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

variable [Finite G] [Finite Q]

theorem le_of_invariant_subset {n : ℕ} (ih : ∀ m < n, Claim.{u, v} m) (π : G →* Q)
    (hπ : Function.Surjective π) (hsol : Group.IsSolvable π.ker) (hQ : IsSS Q)
    {Ω : Type} [Finite Ω] (f : G →* Equiv.Perm Ω) (hf : f.ker ≤ π.ker) (hn : Nat.card Ω = n)
    (O : Set Ω) (hO : ∀ g x, f g x ∈ O ↔ x ∈ O) (hO₁ : O.Nonempty) (hO₂ : Oᶜ.Nonempty) :
    permDeg Q ≤ n := by
  have hOc : ∀ g x, f g x ∈ Oᶜ ↔ x ∈ Oᶜ := fun g x => not_iff_not.mpr (hO g x)
  set H₂ : Subgroup G := (restrictHom f O hO).ker with hH₂def
  have hH₂ : H₂.Normal := MonoidHom.normal_ker _
  set N : Subgroup Q := H₂.map π with hNdef
  have hN : N.Normal := Subgroup.Normal.map hH₂ π hπ
  set C : Subgroup Q := Subgroup.centralizer (N : Set Q) with hCdef
  have hC : C.Normal := by
    have := hN
    exact Subgroup.normal_centralizer
  obtain ⟨hNC1, hNC2⟩ := hQ N hN
  have hcard := card_add_card_compl O
  have h1 : 0 < Nat.card O := by
    obtain ⟨x, hx⟩ := hO₁
    exact Nat.card_pos_iff.mpr ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
  have h2 : 0 < Nat.card (Oᶜ : Set Ω) := by
    obtain ⟨x, hx⟩ := hO₂
    exact Nat.card_pos_iff.mpr ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
  have hA : permDeg N ≤ Nat.card (Oᶜ : Set Ω) := by
    refine ih (Nat.card (Oᶜ : Set Ω)) (by omega) H₂ N (π.subgroupMap H₂)
      (π.subgroupMap_surjective H₂) ?_ (hQ.subgroup_of_normal N) (Oᶜ : Set Ω)
      ((restrictHom f Oᶜ hOc).comp H₂.subtype) ?_ rfl
    · rw [ker_subgroupMap]
      exact isSolvable_subgroupOf _ _
    · intro x hx
      have hx2 : (x : G) ∈ (restrictHom f Oᶜ hOc).ker := hx
      have hx1 : (x : G) ∈ (restrictHom f O hO).ker := x.2
      rw [mem_ker_restrictHom] at hx1 hx2
      have hfx : f x = 1 := by
        ext y
        by_cases hy : y ∈ O
        · exact hx1 y hy
        · exact hx2 y hy
      rw [ker_subgroupMap, Subgroup.mem_subgroupOf]
      exact hf (MonoidHom.mem_ker.mpr hfx)
  have hB : permDeg C ≤ Nat.card O := by
    refine ih (Nat.card O) (by omega) (C.comap π) C (π.subgroupComap C)
      (MonoidHom.subgroupComap_surjective π C hπ) ?_ (hQ.subgroup_of_normal C) O
      ((restrictHom f O hO).comp (C.comap π).subtype) ?_ rfl
    · rw [ker_subgroupComap]
      exact isSolvable_subgroupOf _ _
    · intro x hx
      have hx1 : (x : G) ∈ (restrictHom f O hO).ker := hx
      have hxN : π x ∈ N := Subgroup.mem_map_of_mem π hx1
      have hxC : π x ∈ C := x.2
      have hNC1' : N ⊓ C = ⊥ := hNC1
      have hmem : π x ∈ N ⊓ C := Subgroup.mem_inf.mpr ⟨hxN, hxC⟩
      rw [hNC1', Subgroup.mem_bot] at hmem
      rw [ker_subgroupComap, Subgroup.mem_subgroupOf]
      exact hmem
  calc permDeg Q ≤ permDeg N + permDeg C := permDeg_le_add N hNC1 hNC2
    _ ≤ Nat.card (Oᶜ : Set Ω) + Nat.card O := add_le_add hA hB
    _ = n := by rw [add_comm, hcard, hn]

theorem le_of_kernel_transitive {n : ℕ} (ih : ∀ m < n, Claim.{u, v} m) (π : G →* Q)
    (hπ : Function.Surjective π) (hsol : Group.IsSolvable π.ker) (hQ : IsSS Q)
    {Ω : Type} [Finite Ω] (f : G →* Equiv.Perm Ω) (hf : f.ker ≤ π.ker) (hn : Nat.card Ω = n)
    (hR : ∀ x y : Ω, ∃ r ∈ π.ker, f r x = y) (a : Ω) : permDeg Q ≤ n := by
  set Ga : Subgroup G := pointFix f {a} with hGa
  have hGa' : ∀ g, g ∈ Ga ↔ f g a = a := fun g => by simp [hGa, mem_pointFix]
  let ρ : Ga →* Q := π.comp Ga.subtype
  have hρ : Function.Surjective ρ := by
    intro q
    obtain ⟨g, rfl⟩ := hπ q
    obtain ⟨r, hr, hra⟩ := hR a (f g a)
    refine ⟨⟨r⁻¹ * g, ?_⟩, ?_⟩
    · rw [hGa', map_mul, Equiv.Perm.mul_apply, ← hra, ← Equiv.Perm.mul_apply, ← map_mul,
        inv_mul_cancel, map_one]
      rfl
    · show π (r⁻¹ * g) = π g
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hr, inv_one, one_mul]
  have hinv : ∀ g : Ga, ∀ x, (f.comp Ga.subtype) g x ∈ ({a}ᶜ : Set Ω) ↔
      x ∈ ({a}ᶜ : Set Ω) := by
    intro g x
    have hga : f g a = a := (hGa' g).mp g.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · intro h hx
      exact h (by rw [hx, hga])
    · intro h hx
      exact h ((f g).injective (hx.trans hga.symm))
  have hcard := card_add_card_compl ({a} : Set Ω)
  have h1 : Nat.card ({a} : Set Ω) = 1 := Nat.card_unique
  have hlt : Nat.card (({a} : Set Ω)ᶜ : Set Ω) < n := by omega
  have hmain : permDeg Q ≤ Nat.card (({a} : Set Ω)ᶜ : Set Ω) := by
    refine ih _ hlt Ga Q ρ hρ ?_ hQ (({a} : Set Ω)ᶜ : Set Ω)
      (restrictHom (f.comp Ga.subtype) ({a} : Set Ω)ᶜ hinv) ?_ rfl
    · show Group.IsSolvable (π.ker.subgroupOf Ga)
      exact isSolvable_subgroupOf π.ker Ga
    · intro x hx
      have hx1 := (mem_ker_restrictHom (f.comp Ga.subtype) _ hinv x).mp hx
      have hxa : f x a = a := (hGa' x).mp x.2
      have hfx : f x = 1 := by
        ext y
        by_cases hy : y = a
        · rw [hy]
          exact hxa
        · exact hx1 y hy
      exact hf (MonoidHom.mem_ker.mpr hfx)
  omega

theorem le_of_blocks {n : ℕ} (ih : ∀ m < n, Claim.{u, v} m) (π : G →* Q)
    (hπ : Function.Surjective π) (hsol : Group.IsSolvable π.ker) (hQ : IsSS Q)
    {Ω : Type} [Finite Ω] (f : G →* Equiv.Perm Ω) (hf : f.ker ≤ π.ker) (hn : Nat.card Ω = n)
    (ht : ∀ x y : Ω, ∃ g, f g x = y) (hA : ¬ ∀ r ∈ π.ker, f r = 1)
    (a b : Ω) (hab : ∀ r ∈ π.ker, f r a ≠ b) : permDeg Q ≤ n := by
  classical
  let _ : MulAction G Ω := MulAction.compHom Ω f
  have hsmul : ∀ g x, g • x = f g x := fun _ _ => rfl
  have _ : MulAction.IsPretransitive G Ω := ⟨fun x y => ht x y⟩
  let B : Set Ω := MulAction.orbit π.ker a
  have hB : MulAction.IsBlock G B := MulAction.IsBlock.orbit_of_normal a
  let S : Set (Set Ω) := MulAction.orbit G B
  have hcount : B.ncard * S.ncard = Nat.card Ω :=
    hB.ncard_block_mul_ncard_orbit_eq ⟨a, MulAction.mem_orbit_self a⟩
  have hBmem : ∀ x, x ∈ B ↔ ∃ r ∈ π.ker, f r a = x := by
    intro x
    simp only [B, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, r.2, hr⟩
    · rintro ⟨r, hr, h⟩
      exact ⟨⟨r, hr⟩, h⟩
  have hSmem : ∀ Γ : Set Ω, Γ ∈ S ↔ ∃ g : G, g • B = Γ := fun Γ => MulAction.mem_orbit_iff
  have hBS : B ∈ S := (hSmem B).mpr ⟨1, one_smul G B⟩
  have hsmulset : ∀ (g : G) (Γ : Set Ω) (x : Ω), f g x ∈ g • Γ ↔ x ∈ Γ := by
    intro g Γ x
    exact Set.smul_mem_smul_set_iff
  have hRB : ∀ r ∈ π.ker, r • B = B := by
    intro r hr
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, hsmul, hBmem, hBmem]
    constructor
    · rintro ⟨r', hr', h⟩
      refine ⟨r * r', mul_mem hr hr', ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, h, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel,
        map_one]
      rfl
    · rintro ⟨r', hr', h⟩
      refine ⟨r⁻¹ * r', mul_mem (inv_mem hr) hr', ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, h]
  have hSinv : ∀ (g : G) (Γ : Set Ω), g • Γ ∈ S ↔ Γ ∈ S := by
    intro g Γ
    rw [hSmem, hSmem]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨g⁻¹ * h, ?_⟩
      rw [mul_smul, hh, inv_smul_smul]
    · rintro ⟨h, rfl⟩
      exact ⟨g * h, mul_smul g h B⟩
  let τ : G →* Equiv.Perm (Set Ω) := MulAction.toPermHom G (Set Ω)
  have hτ : ∀ (g : G) (Γ : Set Ω), τ g Γ = g • Γ := fun _ _ => rfl
  let ρ : G →* Equiv.Perm S := restrictHom τ S (fun g Γ => by rw [hτ]; exact hSinv g Γ)
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup G, K = ρ.ker := ⟨_, rfl⟩
  have hKn : K.Normal := hKdef ▸ MonoidHom.normal_ker ρ
  have hKmem : ∀ g, g ∈ K ↔ ∀ Γ ∈ S, g • Γ = Γ := by
    intro g
    rw [hKdef, mem_ker_restrictHom]
    simp only [hτ]
  have hRK : π.ker ≤ K := by
    intro r hr
    rw [hKmem]
    intro Γ hΓ
    obtain ⟨g, rfl⟩ := (hSmem Γ).mp hΓ
    have h1 : (g⁻¹ * r * g) • B = B := hRB _ (by simpa using (π.normal_ker.conj_mem r hr g⁻¹))
    calc r • (g • B) = g • ((g⁻¹ * r * g) • B) := by
          rw [← mul_smul, ← mul_smul]
          simp [mul_assoc]
      _ = g • B := by rw [h1]
  have hinv : ∀ Γ ∈ S, ∀ k ∈ K, ∀ x, f k x ∈ Γ ↔ x ∈ Γ := by
    intro Γ hΓ k hk x
    have h := hsmulset k Γ x
    rwa [(hKmem k).mp hk Γ hΓ] at h
  have hcov : ∀ x, ∃ Γ ∈ S, x ∈ Γ := by
    intro x
    obtain ⟨g, hg⟩ := ht a x
    refine ⟨g • B, (hSmem _).mpr ⟨g, rfl⟩, ?_⟩
    rw [← hg]
    exact (hsmulset g B a).mpr ((hBmem a).mpr ⟨1, one_mem _, by simp⟩)
  have htrans : ∀ Γ ∈ S, ∀ Γ' ∈ S, ∃ g : G, ∀ x, f g x ∈ Γ' ↔ x ∈ Γ := by
    intro Γ hΓ Γ' hΓ'
    obtain ⟨g₁, rfl⟩ := (hSmem Γ).mp hΓ
    obtain ⟨g₂, rfl⟩ := (hSmem Γ').mp hΓ'
    refine ⟨g₂ * g₁⁻¹, fun x => ?_⟩
    have h := hsmulset (g₂ * g₁⁻¹) (g₁ • B) x
    rwa [← mul_smul, mul_assoc, inv_mul_cancel, mul_one] at h
  have hker := kernel_block_le π hπ hQ f hf K hRK S hinv hcov htrans hBS
  have hfin : S.Finite := Set.toFinite S
  have haB : a ∈ B := (hBmem a).mpr ⟨1, one_mem _, by simp⟩
  have hd2 : 2 ≤ B.ncard := by
    have h1 : ∃ r ∈ π.ker, f r a ≠ a := by
      by_contra hcon
      push Not at hcon
      apply hA
      intro r hr
      ext z
      obtain ⟨g, rfl⟩ := ht a z
      have hr' : g⁻¹ * r * g ∈ π.ker := by simpa using π.normal_ker.conj_mem r hr g⁻¹
      have h2 := hcon _ hr'
      have e : f r (f g a) = f g (f (g⁻¹ * r * g) a) := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, ← Equiv.Perm.mul_apply, ← map_mul]
        congr 2
        group
      rw [Equiv.Perm.one_apply, e, h2]
    obtain ⟨r, hr, hra⟩ := h1
    have hyB : f r a ∈ B := (hBmem _).mpr ⟨r, hr, rfl⟩
    have hsub : ({a, f r a} : Set Ω) ⊆ B := by
      intro x hx
      rcases hx with rfl | rfl
      · exact haB
      · exact hyB
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite B)
    rwa [Set.ncard_pair (Ne.symm hra)] at h3
  have hs2 : 2 ≤ S.ncard := by
    obtain ⟨g, hg⟩ := ht a b
    have hΓS : g • B ∈ S := (hSmem _).mpr ⟨g, rfl⟩
    have hbΓ : b ∈ g • B := by
      rw [← hg]
      exact (hsmulset g B a).mpr haB
    have hbB : b ∉ B := fun h => by
      obtain ⟨r, hr, e⟩ := (hBmem b).mp h
      exact hab r hr e
    have hne : g • B ≠ B := fun h => hbB (h ▸ hbΓ)
    have hsub : ({g • B, B} : Set (Set Ω)) ⊆ S := by
      intro x hx
      rcases hx with rfl | rfl
      · exact hΓS
      · exact hBS
    have h3 := Set.ncard_le_ncard hsub hfin
    rwa [Set.ncard_pair hne] at h3
  have hds : B.ncard * S.ncard = n := hcount.trans hn
  have hdn : B.ncard < n := by nlinarith
  have hsn : S.ncard < n := by nlinarith
  have hdsn : B.ncard + S.ncard ≤ n := by nlinarith
  set Kb : Subgroup Q := K.map π with hKbdef
  have hKb : Kb.Normal := Subgroup.Normal.map hKn π hπ
  set C : Subgroup Q := Subgroup.centralizer (Kb : Set Q) with hCdef
  have hC : C.Normal := by
    have := hKb
    exact Subgroup.normal_centralizer
  obtain ⟨hKC1, hKC2⟩ := hQ Kb hKb
  have hKC1' : Kb ⊓ C = ⊥ := hKC1
  have hA' : permDeg Kb ≤ B.ncard := by
    have hinvB : ∀ k : K, ∀ x, (f.comp K.subtype) k x ∈ B ↔ x ∈ B :=
      fun k x => hinv B hBS k k.2 x
    have hcardB : Nat.card B = B.ncard := Nat.card_coe_set_eq B
    have h := ih B.ncard hdn K Kb (π.subgroupMap K) (π.subgroupMap_surjective K) ?_
      (hQ.subgroup_of_normal Kb) B (restrictHom (f.comp K.subtype) B hinvB) ?_ hcardB
    · exact h
    · rw [ker_subgroupMap]
      exact isSolvable_subgroupOf _ _
    · intro x hx
      have hx1 := (mem_ker_restrictHom (f.comp K.subtype) B hinvB x).mp hx
      have hxf : (x : G) ∈ K ⊓ pointFix f B :=
        Subgroup.mem_inf.mpr ⟨x.2, fun y hy => hx1 y hy⟩
      rw [ker_subgroupMap, Subgroup.mem_subgroupOf]
      exact hker hxf
  have hB' : permDeg C ≤ S.ncard := by
    have hcardS : Nat.card S = S.ncard := Nat.card_coe_set_eq S
    have h := ih S.ncard hsn (C.comap π) C (π.subgroupComap C)
      (MonoidHom.subgroupComap_surjective π C hπ) ?_ (hQ.subgroup_of_normal C) S
      (ρ.comp (C.comap π).subtype) ?_ hcardS
    · exact h
    · rw [ker_subgroupComap]
      exact isSolvable_subgroupOf _ _
    · intro z hz
      have hzK : (z : G) ∈ K := by
        rw [hKdef]
        exact hz
      have hzKb : π z ∈ Kb := Subgroup.mem_map_of_mem π hzK
      have hzC : π z ∈ C := z.2
      have hmem : π z ∈ Kb ⊓ C := Subgroup.mem_inf.mpr ⟨hzKb, hzC⟩
      rw [hKC1', Subgroup.mem_bot] at hmem
      rw [ker_subgroupComap, Subgroup.mem_subgroupOf]
      exact hmem
  calc permDeg Q ≤ permDeg Kb + permDeg C := permDeg_le_add Kb hKC1 hKC2
    _ ≤ B.ncard + S.ncard := add_le_add hA' hB'
    _ ≤ n := hdsn

theorem claim_all (n : ℕ) : Claim.{u, v} n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G Q _ _ _ _ π hπ hsol hQ Ω _ f hf hn
    by_cases hA : ∀ r ∈ π.ker, f r = 1
    · have hker : f.ker = π.ker :=
        le_antisymm hf (fun r hr => MonoidHom.mem_ker.mpr (hA r hr))
      rw [← hn]
      exact permDeg_le_of_ker_eq π hπ f hker
    · by_cases ht : ∀ x y : Ω, ∃ g, f g x = y
      · by_cases hRt : ∀ x y : Ω, ∃ r ∈ π.ker, f r x = y
        · have hne : Nonempty Ω := by
            by_contra hne
            rw [not_nonempty_iff] at hne
            refine hA fun r _ => ?_
            ext z
            exact (IsEmpty.false z).elim
          obtain ⟨a⟩ := hne
          exact le_of_kernel_transitive ih π hπ hsol hQ f hf hn hRt a
        · push Not at hRt
          obtain ⟨a, b, hab⟩ := hRt
          exact le_of_blocks ih π hπ hsol hQ f hf hn ht hA a b hab
      · push Not at ht
        obtain ⟨x, y, hxy⟩ := ht
        let O : Set Ω := Set.range fun g : G => f g x
        have hO : ∀ g z, f g z ∈ O ↔ z ∈ O := by
          intro g z
          constructor
          · rintro ⟨h, hh⟩
            have hh' : f h x = f g z := hh
            refine ⟨g⁻¹ * h, ?_⟩
            show f (g⁻¹ * h) x = z
            rw [map_mul, Equiv.Perm.mul_apply, hh', ← Equiv.Perm.mul_apply, ← map_mul,
              inv_mul_cancel, map_one]
            rfl
          · rintro ⟨h, rfl⟩
            refine ⟨g * h, ?_⟩
            show f (g * h) x = f g (f h x)
            rw [map_mul]
            rfl
        exact le_of_invariant_subset ih π hπ hsol hQ f hf hn O hO ⟨x, ⟨1, by simp⟩⟩
          ⟨y, fun ⟨g, hg⟩ => hxy g hg⟩

theorem permDeg_le_card (π : G →* Q) (hπ : Function.Surjective π)
    (hsol : Group.IsSolvable π.ker) (hQ : IsSS Q) {Ω : Type} [Finite Ω] (f : G →* Equiv.Perm Ω)
    (hf : f.ker ≤ π.ker) : permDeg Q ≤ Nat.card Ω :=
  claim_all.{u, v} _ G Q π hπ hsol hQ Ω f hf rfl

end Cases

end CFSG.SignalizerFunctorTheorem.McBride.Near.Deg
