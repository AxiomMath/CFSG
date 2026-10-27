module

public import CFSG.Quasithin.Background.E2TwoProofDefs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique B6

namespace E2P

section Canonical

variable {C : Type} [Group C]

theorem map_centralizer_eq (α : MulAut C) (S : Subgroup C) :
    (Subgroup.centralizer (S : Set C)).map α.toMonoidHom =
      Subgroup.centralizer ((S.map α.toMonoidHom : Subgroup C) : Set C) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have := (Subgroup.mem_centralizer_iff.mp hy) s hs
    simpa using congrArg α this
  · intro hx
    refine ⟨α⁻¹ x, ?_, by simp⟩
    show α⁻¹ x ∈ Subgroup.centralizer (S : Set C)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply α.injective
    have := (Subgroup.mem_centralizer_iff.mp hx) (α s) ⟨s, hs, rfl⟩
    simpa using this

theorem map_zOf (α : MulAut C) (U : Subgroup C) :
    (zOf U).map α.toMonoidHom = zOf (U.map α.toMonoidHom) := by
  unfold zOf
  rw [Subgroup.map_inf _ _ _ α.injective, map_centralizer_eq]

theorem map_centralizer_zOf_eq {α : MulAut C} {U : Subgroup C} (hα : U.map α.toMonoidHom = U) :
    (Subgroup.centralizer (zOf U : Set C)).map α.toMonoidHom =
      Subgroup.centralizer (zOf U : Set C) := by
  rw [map_centralizer_eq, map_zOf, hα]

theorem map_normalizer_centralizer_commutator_eq {α : MulAut C} {U : Subgroup C}
    (hα : U.map α.toMonoidHom = U) :
    (Subgroup.normalizer (Subgroup.centralizer ((⁅U, U⁆ : Subgroup C) : Set C) : Set C)).map
        α.toMonoidHom =
      Subgroup.normalizer (Subgroup.centralizer ((⁅U, U⁆ : Subgroup C) : Set C) : Set C) := by
  rw [Subgroup.map_normalizer_eq_of_bijective _ α.bijective, map_centralizer_eq,
    Subgroup.map_commutator, hα]

theorem le_centralizer_zOf (U : Subgroup C) : U ≤ Subgroup.centralizer (zOf U : Set C) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun _ hw =>
    (Subgroup.mem_centralizer_iff.mp hw.2 x hx).symm

theorem le_normalizer_centralizer_commutator (U : Subgroup C) :
    U ≤ Subgroup.normalizer (Subgroup.centralizer ((⁅U, U⁆ : Subgroup C) : Set C) : Set C) := by
  intro u hu
  have hU : U.map (MulAut.conj u).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hu)
  have hmap : (Subgroup.centralizer ((⁅U, U⁆ : Subgroup C) : Set C)).map
      (MulAut.conj u).toMonoidHom = Subgroup.centralizer ((⁅U, U⁆ : Subgroup C) : Set C) := by
    rw [map_centralizer_eq, Subgroup.map_commutator, hU]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

theorem normalizer_centralizer_ne_top [IsSimpleGroup C] (hnab : ∃ a b : C, a * b ≠ b * a)
    {V : Subgroup C} (hV : V ≠ ⊥) (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) :
    Subgroup.normalizer (Subgroup.centralizer (V : Set C) : Set C) ≠ ⊤ := by
  intro h
  have hn : (Subgroup.centralizer (V : Set C)).Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.centralizer (V : Set C)) with hb | ht
  · apply hV
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Subgroup.centralizer (V : Set C) := Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hcomm y hy x hx
    rw [hb] at this
    exact this
  · apply hV
    rw [eq_bot_iff]
    intro x hx
    have hxc : ∀ y : C, y * x = x * y := fun y => by
      have : y ∈ Subgroup.centralizer (V : Set C) := by rw [ht]; trivial
      exact (Subgroup.mem_centralizer_iff.mp this x hx).symm
    have hz : x ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr hxc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center C) with h0 | h1
    · rw [h0] at hz
      exact hz
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : a ∈ Subgroup.center C := by rw [h1]; trivial
      exact (Subgroup.mem_center_iff.mp this b).symm

end Canonical

section Sylow

variable {G : Type*} [Group G]

theorem isSylowTwoOf_top_of_odd_index {B S : Subgroup G} (hB : Odd B.index)
    (hS : IsSylowTwoOf S B) : IsSylowTwoOf S ⊤ := by
  refine ⟨le_top, hS.2.1, fun hd => ?_⟩
  have h1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [h1, ← Subgroup.relIndex_mul_index hS.1] at hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
  · exact hS.2.2 h
  · exact (Nat.not_even_iff_odd.mpr hB) (even_iff_two_dvd.mpr h)

end Sylow

section Pull

variable {X : Type} [Group X] {K T : Subgroup X} {C : Type} [Group C]

theorem mem_pull_iff (e : ↥K ≃* C) {P : Subgroup C} {x : X} :
    x ∈ (P.map e.symm.toMonoidHom).map K.subtype ↔ ∃ hx : x ∈ K, e ⟨x, hx⟩ ∈ P := by
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨(e.symm c).2, by simpa using hc⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, ⟨e ⟨x, hx⟩, h, by simp⟩, rfl⟩

theorem map_mem_zOf_iff {e : ↥K ≃* C} {U : Subgroup C}
    (hU : ((T ⊓ K).subgroupOf K).map e.toMonoidHom = U) {k : ↥K} :
    e k ∈ zOf U ↔ (k : X) ∈ zOf (T ⊓ K) := by
  have hmemU : ∀ k' : ↥K, e k' ∈ U ↔ (k' : X) ∈ T ⊓ K := fun k' => by
    rw [← hU]
    constructor
    · rintro ⟨s, hs, hse⟩
      have : s = k' := e.injective hse
      rw [← this]
      exact hs
    · intro h
      exact ⟨k', h, rfl⟩
  constructor
  · rintro ⟨hkU, hkC⟩
    refine ⟨(hmemU k).mp hkU, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have htK : t ∈ K := ht.2
    have := Subgroup.mem_centralizer_iff.mp hkC (e ⟨t, htK⟩) ((hmemU ⟨t, htK⟩).mpr ht)
    have h2 := congrArg e.symm this
    simp only [map_mul, MulEquiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  · rintro ⟨hkS, hkC⟩
    refine ⟨(hmemU k).mpr hkS, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    obtain ⟨k', hk'⟩ : ∃ k' : ↥K, e k' = u := by
      rw [← hU] at hu
      obtain ⟨s, -, hs⟩ := hu
      exact ⟨s, hs⟩
    have hk'S : (k' : X) ∈ T ⊓ K := (hmemU k').mp (hk' ▸ hu)
    have := Subgroup.mem_centralizer_iff.mp hkC (k' : X) hk'S
    rw [← hk', ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext this)

theorem pull_centralizer_zOf {e : ↥K ≃* C} {U : Subgroup C}
    (hU : ((T ⊓ K).subgroupOf K).map e.toMonoidHom = U) :
    ((Subgroup.centralizer (zOf U : Set C)).map e.symm.toMonoidHom).map K.subtype =
      K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) := by
  ext x
  rw [mem_pull_iff]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hwK : w ∈ K := hw.1.2
    have := Subgroup.mem_centralizer_iff.mp h (e ⟨w, hwK⟩) ((map_mem_zOf_iff hU).mpr hw)
    have h2 := congrArg e.symm this
    simp only [map_mul, MulEquiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  · rintro ⟨hx, h⟩
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    obtain ⟨k', hk'⟩ : ∃ k' : ↥K, e k' = u := by
      have : u ∈ ((T ⊓ K).subgroupOf K).map e.toMonoidHom := hU ▸ hu.1
      obtain ⟨s, -, hs⟩ := this
      exact ⟨s, hs⟩
    have hk'Z : (k' : X) ∈ zOf (T ⊓ K) := (map_mem_zOf_iff hU).mp (hk' ▸ hu)
    have := Subgroup.mem_centralizer_iff.mp h (k' : X) hk'Z
    rw [← hk', ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext this)

end Pull

end E2P

end CFSG.Quasithin
