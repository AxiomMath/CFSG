module

public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Vol2.Ch11SecABasic
public import CFSG.Quasithin.Vol2.Ch11StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autI_zpowers {V : Subgroup G} (hV : IsElemAbelian 2 V) {a : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) :
    autI hV (Subgroup.zpowers a) = Subgroup.zpowers (convI hV ⟨a, ha⟩) := by
  ext φ
  rw [mem_autI hV, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk)
  · rintro ⟨k, rfl⟩
    exact ⟨⟨a, ha⟩ ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, by simp⟩, map_zpow _ _ _⟩

omit [Finite G] in
theorem card_commV_autI {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(commV (autI hV A)) = Nat.card ↥⁅V, A⁆ := by
  rw [S1417.commutator_eq_map_commV hV hA,
    Subgroup.card_map_of_injective (S1417.inclMod_injective hV)]

omit [Finite G] in
theorem inf_commutator_eq_bot {V A B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (hB : B ≤ Subgroup.normalizer (V : Set G))
    (h : commV (autI hV A) ⊓ commV (autI hV B) = ⊥) : ⁅V, A⁆ ⊓ ⁅V, B⁆ = ⊥ := by
  rw [S1417.commutator_eq_map_commV hV hA, S1417.commutator_eq_map_commV hV hB,
    ← Subgroup.map_inf_eq _ _ _ (S1417.inclMod_injective hV), h, Subgroup.map_bot]

omit [Finite G] in
theorem VZ_eq_conjClosure {T H K : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hH : K ⊔ T = H) : VZ T H = conjClosure (quasithinOmegaOneCenter T) K := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    rw [← hH, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hh
    obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hh
    have hzt : t * z = z * t :=
      (Subgroup.mem_centralizer_iff.mp (E3.omegaOneCenter_le_inf_centralizer T hz).2 t ht)
    have e : k * t * z * (k * t)⁻¹ = k * z * k⁻¹ := by
      rw [mul_assoc k t z, hzt]
      group
    rw [e]
    exact mem_conjClosure hk hz
  · exact conjClosure_mono le_rfl (hH ▸ le_sup_left)

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem twoResidual_not_le_centralizer (hyp : Hyp11 G T L I n) {V₁ H : Subgroup G}
    (h31 : Hyp11_3_1 T L I n V₁ H) :
    ¬ twoResidual H ≤ Subgroup.centralizer (VZ T H : Set G) := by
  intro hle
  apply h31.moves
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hTS : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow h31.hstar.1.1
  rw [← sup_twoResidual_eq hTS]
  refine sup_le (fun t ht => Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
    (hle.trans (Subgroup.centralizer_le (le_conjClosure _ _)))
  exact (Subgroup.mem_centralizer_iff.mp (E3.omegaOneCenter_le_inf_centralizer T hz).2 t ht).symm

theorem inf_centralizer_VZ_le (h331 : Stmt3_3_1) (hyp : Hyp11 G T L I n) {V₁ H : Subgroup G}
    (h31 : Hyp11_3_1 T L I n V₁ H) :
    T ⊓ Subgroup.centralizer (VZ T H : Set G) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := minParabolic_of_isHStar h331 hyp h31.hstar
  have hHV : H ≤ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H
  have hCn : H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (VZ T H : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hHV)
  have hK : ¬ twoResidual H ≤ H ⊓ Subgroup.centralizer (VZ T H : Set G) := fun hle =>
    twoResidual_not_le_centralizer hyp h31 (hle.trans inf_le_right)
  have hCJ := hmp.le_kerIn_of_not_twoResidual_le inf_le_left hCn hK
  have hSyl := hmp.isSylowTwoOf_pCoreOf_kerIn
  have hP : T ⊓ Subgroup.centralizer (VZ T H : Set G) ≤
      kerIn (H ⊓ Subgroup.normalizer (L : Set G)) H :=
    fun x hx => hCJ ⟨h31.hstar.1.1 hx.1, hx.2⟩
  have hP2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (VZ T H : Set G)) :=
    hyp.fsu.sylow.1.to_le inf_le_left
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hSyl hP hP2
  have hhN : h ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hmp.kerIn_le_H hh)
  intro x hx
  have h1 : h * x * h⁻¹ ∈ pCoreOf 2 H := hle (mem_cjSub.mpr (by simpa [mul_assoc] using hx))
  exact (Subgroup.mem_normalizer_iff.mp hhN x).mpr h1

end CFSG.Quasithin.Vol2.Ch11.SecB
