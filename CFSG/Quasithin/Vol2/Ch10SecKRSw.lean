module

public import CFSG.Quasithin.Vol2.Ch10SecKRSo
public import CFSG.Quasithin.Vol2.Ch10SecQ9G17

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {D : Subgroup G} {d : G}
    (h : ∀ z ∈ D, d * z * d⁻¹ ∈ D) : d ∈ Subgroup.normalizer (D : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨h z, fun hz => ?_⟩
  let f : ↥D → ↥D := fun y => ⟨d * y * d⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hz⟩
  have := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at this
  exact this ▸ y.2

theorem exists_conj_iff {J R : Subgroup G} (ρ : ↥J →* SL5) (hρ : Function.Surjective ρ)
    (hR : IsSylowTwoOf R J) (hker : ∀ j : ↥J, ρ j = 1 → (j : G) ∈ R) :
    ∃ A : SL5, ∀ j : ↥J, A * ρ j * A⁻¹ ∈ uniSL 5 ↔ (j : G) ∈ R := by
  obtain ⟨A, hA⟩ := exists_conj_uniSL (image_isSylowTwoOf hR ρ hρ)
  refine ⟨A, fun j => ?_⟩
  rw [← hA]
  constructor
  · rintro ⟨r, hr, hrj⟩
    have h1 : ρ (r⁻¹ * j) = 1 := by rw [map_mul, map_inv, hrj, inv_mul_cancel]
    have h2 := hker _ h1
    have h3 : (j : G) = (r : G) * ((r⁻¹ * j : ↥J) : G) := by simp
    rw [h3]
    exact R.mul_mem (Subgroup.mem_subgroupOf.mp hr) h2
  · intro hj
    exact ⟨j, Subgroup.mem_subgroupOf.mpr hj, rfl⟩

variable [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.isSylowTwoOf_inf_J (c : Conf T L I t w J) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({w} : Set G) ⊓ J) J :=
  A4.isSylowTwoOf_inf_normal c.sylow c.J_le
    ((Subgroup.normal_subgroupOf_iff_le_normalizer c.J_le).mp c.normal)

theorem Conf.pCoreOf_J_le (c : Conf T L I t w J) :
    pCoreOf 2 J ≤ T ⊓ Subgroup.centralizer ({w} : Set G) ⊓ J :=
  A4.le_of_normal_of_isSylowTwoOf (Conf.isSylowTwoOf_inf_J c)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 J)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 J)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)

theorem Conf.pCoreOf_L_le (c : Conf T L I t w J)
    (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L) :
    pCoreOf 2 L ≤ T ⊓ Subgroup.centralizer ({w} : Set G) := by
  have hS : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({w} : Set G))
      (L ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) :=
    A4.isSylowTwoOf_mono c.sylow le_sup_right (sup_le (c.le.trans c.J_le) inf_le_right)
  have hN : L ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      ((hTw.le.trans inf_le_right).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hle : pCoreOf 2 L ≤ L ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left
  exact A4.le_of_normal_of_isSylowTwoOf hS hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hN)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem Conf.exists_altCoord_normalized (c : Conf T L I t w J)
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (C : AltCoord J (VI T L I J w)) :
    ∃ C' : AltCoord J (VI T L I J w), ∀ j : ↥J,
      C'.ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨A, hA⟩ := exists_conj_iff C.ρ C.ρ_surj (Conf.isSylowTwoOf_inf_J c) fun j hj =>
    Conf.pCoreOf_J_le c (hCJ ▸ (⟨j.2, C.mem_centralizer_of_rho hj⟩ :
      (j : G) ∈ J ⊓ Subgroup.centralizer (VI T L I J w : Set G)))
  refine ⟨C.conjBy A, fun j => ?_⟩
  rw [C.conjBy_ρ, hA j]
  exact ⟨fun h => h.1, fun h => ⟨h, j.2⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
