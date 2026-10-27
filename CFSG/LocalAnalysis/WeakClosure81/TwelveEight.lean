module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveEightA
public import CFSG.LocalAnalysis.WeakClosure81.TwelvePartTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section Modules

variable {G : Type} [Group G]

private def b12_TwelveEight_stab (ρ : G →* LGL 2 V) (v : V) : Subgroup G where
  carrier := {x | ρ x v = v}
  one_mem' := by
    change ρ 1 v = v
    rw [map_one]
    rfl
  mul_mem' := fun {s t} hs ht => by
    change ρ (s * t) v = v
    rw [map_mul, LinearEquiv.mul_apply, ht, hs]
  inv_mem' := fun {s} hs => by
    change ρ s⁻¹ v = v
    rw [map_inv]
    have h : (ρ s).symm ((ρ s) v) = (ρ s).symm v := congrArg (ρ s).symm hs
    rw [LinearEquiv.symm_apply_apply] at h
    exact h.symm

theorem mem_fixSub_range_of_sup_eq_top (ρ : G →* LGL 2 V) {H₁ H₂ : Subgroup G}
    (h : H₁ ⊔ H₂ = ⊤) {v : V} (h₁ : ∀ x ∈ H₁, ρ x v = v) (h₂ : ∀ x ∈ H₂, ρ x v = v) :
    v ∈ fixSub ρ.range := by
  have hle : H₁ ⊔ H₂ ≤ b12_TwelveEight_stab ρ v :=
    sup_le (fun x hx => h₁ x hx) (fun x hx => h₂ x hx)
  intro t ht
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ht
  have hx : x ∈ H₁ ⊔ H₂ := by rw [h]; exact Subgroup.mem_top x
  exact hle hx

theorem exists_odd_decomp (ρ : G →* LGL 2 V) {y a : G} (hy : Odd (orderOf y))
    (hinv : a * y * a⁻¹ = y⁻¹) {u : V} (hau : ρ a u = u) :
    ∃ u₁ u₂ : V, u = u₁ + u₂ ∧ ρ y u₁ = u₁ ∧ ρ a u₁ = u₁ ∧ u₂ ∈ commSub ρ.range ∧
      ρ a u₂ = u₂ := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let Q : Subgroup (LGL 2 V) := Subgroup.zpowers (ρ y)
  have hcard : Nat.card Q = orderOf (ρ y) := Nat.card_zpowers (ρ y)
  have hdvd : orderOf (ρ y) ∣ orderOf y := orderOf_map_dvd ρ y
  have hoddQ : Odd (Nat.card Q) := by
    rw [hcard]
    exact Odd.of_dvd_nat hy hdvd
  have hcop : Nat.Coprime 2 (Nat.card Q) := Nat.coprime_two_left.mpr hoddQ
  have hcompl := isCompl_fixSub_commSub (p := 2) (Q := Q) hcop
  have hu : u ∈ fixSub Q ⊔ commSub Q := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u₁, hu₁, u₂, hu₂, huv⟩ := Submodule.mem_sup.mp hu
  have hconj : ρ a * ρ y * (ρ a)⁻¹ = (ρ y)⁻¹ := by
    have h1 : ρ (a * y * a⁻¹) = ρ a * ρ y * (ρ a)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [← h1, hinv, map_inv]
  have hmapconj : Q.map (MulAut.conj (ρ a)) = Q := by
    have hmap := MonoidHom.map_zpowers (MulAut.conj (ρ a) : LGL 2 V →* LGL 2 V) (ρ y)
    change (Subgroup.zpowers (ρ y)).map (MulAut.conj (ρ a)) = Subgroup.zpowers (ρ y)
    rw [hmap]
    have hgen : (MulAut.conj (ρ a) : LGL 2 V →* LGL 2 V) (ρ y) = (ρ y)⁻¹ := by
      change MulAut.conj (ρ a) (ρ y) = (ρ y)⁻¹
      exact (MulAut.conj_apply (ρ a) (ρ y)).trans hconj
    rw [hgen, Subgroup.zpowers_inv]
  have hnorm : ρ a ∈ Subgroup.normalizer (Q : Set (LGL 2 V)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapconj
  have hfix₁ : ρ a u₁ ∈ fixSub Q := map_mem_fixSub_of_mem_normalizer Q hnorm hu₁
  have hcomm₂ : ρ a u₂ ∈ commSub Q := map_mem_commSub_of_mem_normalizer Q hnorm hu₂
  have hdiff : ρ a u₁ - u₁ = u₂ - ρ a u₂ := by
    have h1 : ρ a (u₁ + u₂) = u₁ + u₂ := by
      rw [huv]
      exact hau
    rw [map_add] at h1
    have h0 : (ρ a u₁ - u₁) - (u₂ - ρ a u₂) = 0 := by
      rw [show (ρ a u₁ - u₁) - (u₂ - ρ a u₂) = (ρ a u₁ + ρ a u₂) - (u₁ + u₂) by abel,
        h1, sub_self]
    exact sub_eq_zero.mp h0
  have hmem : ρ a u₁ - u₁ ∈ fixSub Q ⊓ commSub Q :=
    ⟨Submodule.sub_mem _ hfix₁ hu₁, hdiff.symm ▸ Submodule.sub_mem _ hu₂ hcomm₂⟩
  rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
  have hau₁ : ρ a u₁ = u₁ := sub_eq_zero.mp hmem
  have hau₂ : ρ a u₂ = u₂ := by
    have h1 : ρ a (u₁ + u₂) = u₁ + u₂ := by
      rw [huv]
      exact hau
    rw [map_add, hau₁] at h1
    exact add_left_cancel h1
  refine ⟨u₁, u₂, huv.symm, hu₁ (ρ y) (Subgroup.mem_zpowers (ρ y)), hau₁, ?_, hau₂⟩
  exact commSub_mono Q ρ.range
    (Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨y, rfl⟩)) hu₂

end Modules

section PartTwo

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.cE_range_le_commSub (h : Setting12Two A M n) (ρ : G →* LGL 2 V)
    (hq : RepQuad ρ A) : cE ρ.range ≤ commSub (A.map ρ) := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
    by_contra hc
    rw [not_exists] at hc
    exact h.M_ne (eq_top_iff.mpr fun x _ => by simpa using hc x)
  have hC := twelveFive_partTwo h ρ hq hg
  intro z hz
  have hzG : z ∈ commSub ρ.range := cE_le_commSub ρ.range hz
  have hzsup : z ∈ commSub (A.map ρ) ⊔ commSub (cj (ρ g) (A.map ρ)) := by
    rw [← hC.1]
    exact hzG
  obtain ⟨x, hx, x', hx', hxsum⟩ := Submodule.mem_sup.mp hzsup
  have hzq : (cE ρ.range).mkQ z = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hz
  have hxq : (cE ρ.range).mkQ x = 0 := by
    have h2 : (cE ρ.range).mkQ x ∈
        (commSub (A.map ρ)).map (cE ρ.range).mkQ ⊓
          (commSub (cj (ρ g) (A.map ρ))).map (cE ρ.range).mkQ := by
      refine ⟨Submodule.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
      have hx'q : (cE ρ.range).mkQ x = (cE ρ.range).mkQ (-x') := by
        rw [map_neg, eq_neg_iff_add_eq_zero]
        rw [← map_add, hxsum, hzq]
      rw [hx'q]
      exact Submodule.mem_map.mpr ⟨-x', Submodule.neg_mem _ hx', rfl⟩
    rw [hC.2.1, Submodule.mem_bot] at h2
    exact h2
  have hxW : x ∈ cE ρ.range := (Submodule.Quotient.mk_eq_zero _).mp hxq
  have hx'W : x' ∈ cE ρ.range := by
    have h1 : z - x ∈ cE ρ.range := Submodule.sub_mem _ hz hxW
    have h2 : z - x = x' := by rw [← hxsum]; abel
    rwa [h2] at h1
  have hx'r : x' ∈ (commSub (A.map ρ)).map ((ρ g : LGL 2 V) : V →ₗ[ZMod 2] V) := by
    rw [← commSub_cj (A.map ρ) (ρ g)]
    exact hx'
  obtain ⟨x'', hx'', hx''eq⟩ := Submodule.mem_map.mp hx'r
  change ρ g x'' = x' at hx''eq
  have hg'mem : ρ g ∈ ρ.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hx'fix : x' ∈ fixSub ρ.range := cE_le_fixSub ρ.range hx'W
  have hx''eq' : x'' = x' := by
    calc x'' = (ρ g)⁻¹ (ρ g x'') := (LinearEquiv.symm_apply_apply (ρ g) x'').symm
      _ = (ρ g)⁻¹ x' := by rw [hx''eq]
      _ = x' := hx'fix (ρ g)⁻¹ ((ρ.range).inv_mem hg'mem)
  have hx'cA : x' ∈ commSub (A.map ρ) := by
    rw [← hx''eq']
    exact hx''
  rw [← hxsum]
  exact Submodule.add_mem _ hx hx'cA

theorem Setting12Two.fixSub_inf_commSub (h : Setting12Two A M n) (ρ : G →* LGL 2 V)
    (hq : RepQuad ρ A) : fixSub (A.map ρ) ⊓ commSub ρ.range = commSub (A.map ρ) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨a, ha, haK⟩ : ∃ a ∈ A, a ∉ CFSG.Quasithin.kerIn M ⊤ := by
      by_contra hc
      rw [not_exists] at hc
      apply h.not_le_ker
      intro a ha
      by_contra haK
      exact hc a ⟨ha, haK⟩
    obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
      by_contra hc
      rw [not_exists] at hc
      exact h.M_ne (eq_top_iff.mpr fun x _ => by simpa using hc x)
    have hfix3 := (twelveFive_partTwo h ρ hq hg).2.2.1 (ρ a)
      (Subgroup.mem_map_of_mem ρ ha) ⟨a, ha, haK, rfl⟩
    have hafix : ρ a v = v := hv.1 (ρ a) (Subgroup.mem_map_of_mem ρ ha)
    have hvfix : v ∈ fixMod (cE ρ.range) (ρ a) := by
      rw [mem_fixMod, hafix, sub_self]
      exact (cE ρ.range).zero_mem
    have hvin : v ∈ fixMod (cE ρ.range) (ρ a) ⊓ commSub ρ.range := ⟨hvfix, hv.2⟩
    rw [hfix3] at hvin
    obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hvin
    have hzA : z ∈ commSub (A.map ρ) := Setting12Two.cE_range_le_commSub h ρ hq hz
    rw [← hxz]
    exact Submodule.add_mem _ hx hzA
  · exact le_inf (commSub_le_fixSub_of_quadratic hq)
      (commSub_mono (A.map ρ) ρ.range (Subgroup.map_le_range ρ A))

theorem Setting12Two.fixSub_le_commSub_sup_fixSub (h : Setting12Two A M n)
    (hA : IsElemAbelian 2 A) (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) :
    fixSub (A.map ρ) ≤ commSub (A.map ρ) ⊔ fixSub ρ.range := by
  intro u hu
  obtain ⟨a, ha, haK⟩ : ∃ a ∈ A, a ∉ CFSG.Quasithin.kerIn M ⊤ := by
    by_contra hc
    rw [not_exists] at hc
    apply h.not_le_ker
    intro a ha
    by_contra haK
    exact hc a ⟨ha, haK⟩
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
    by_contra hc
    rw [not_exists] at hc
    exact h.M_ne (eq_top_iff.mpr fun x _ => by simpa using hc x)
  obtain ⟨_, y, _, _, _, _, hyodd, hyM, hinv⟩ :=
    Setting12Two.exists_inverted_odd h hA ha haK hg
  have hau : ρ a u = u := hu (ρ a) (Subgroup.mem_map_of_mem ρ ha)
  obtain ⟨u₁, u₂, huv, hyu₁, hau₁, hu₂, hau₂⟩ := exists_odd_decomp ρ hyodd hinv hau
  have hfix3 := (twelveFive_partTwo h ρ hq hg).2.2.1 (ρ a)
    (Subgroup.mem_map_of_mem ρ ha) ⟨a, ha, haK, rfl⟩
  have hu₂fix : u₂ ∈ fixMod (cE ρ.range) (ρ a) := by
    rw [mem_fixMod, hau₂, sub_self]
    exact (cE ρ.range).zero_mem
  have hu₂sup : u₂ ∈ commSub (A.map ρ) ⊔ cE ρ.range := by
    rw [← hfix3]
    exact ⟨hu₂fix, hu₂⟩
  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hu₂sup
  have hxA (b : G) (hb : b ∈ A) : ρ b x = x :=
    commSub_le_fixSub_of_quadratic hq hx (ρ b) (Subgroup.mem_map_of_mem ρ hb)
  have hzG (b : G) (_hb : b ∈ A) : ρ b z = z :=
    cE_le_fixSub ρ.range hz (ρ b) (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  have hu_eq : u = u₁ + x + z := by rw [huv, ← hxz]; abel
  have hu₁_eq : u₁ = u - x - z := by rw [hu_eq]; abel
  have hb_fix (b : G) (hb : b ∈ A) : ρ b u₁ = u₁ := by
    simp only [hu₁_eq, map_sub, hu (ρ b) (Subgroup.mem_map_of_mem ρ hb), hxA b hb, hzG b hb]
  have hyinv : ρ y⁻¹ u₁ = u₁ := by
    rw [map_inv]
    have h : (ρ y).symm ((ρ y) u₁) = (ρ y).symm u₁ := congrArg (ρ y).symm hyu₁
    rw [LinearEquiv.symm_apply_apply] at h
    exact h.symm
  have hconj_fix : ρ (y⁻¹ * a * (y⁻¹)⁻¹) u₁ = u₁ := by
    simp only [inv_inv, map_mul, LinearEquiv.mul_apply, hyu₁, hau₁, hyinv]
  have hyinvM : y⁻¹ ∉ M := fun hh => hyM (by simpa using M.inv_mem hh)
  have htop : Subgroup.zpowers (y⁻¹ * a * (y⁻¹)⁻¹) ⊔ A = ⊤ :=
    Setting12Two.zpowers_conj_sup_eq_top h (g := y⁻¹) (a := a) hyinvM ha haK
  have hstab : ∀ b ∈ Subgroup.zpowers (y⁻¹ * a * (y⁻¹)⁻¹), ρ b u₁ = u₁ := by
    intro b hb
    have hle : Subgroup.zpowers (y⁻¹ * a * (y⁻¹)⁻¹) ≤ b12_TwelveEight_stab ρ u₁ :=
      (Subgroup.zpowers_le (H := b12_TwelveEight_stab ρ u₁)).mpr hconj_fix
    exact hle hb
  have hu₁G : u₁ ∈ fixSub ρ.range :=
    mem_fixSub_range_of_sup_eq_top ρ htop hstab (fun b hb => hb_fix b hb)
  refine Submodule.mem_sup.mpr
    ⟨x, hx, z + u₁, Submodule.add_mem _ (cE_le_fixSub ρ.range hz) hu₁G, ?_⟩
  rw [hu_eq]
  abel

end PartTwo

end CFSG.LocalAnalysis.WeakClosure81