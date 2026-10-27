module

public import CFSG.Quasithin.Vol2.Ch11SecHP2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec

variable {G : Type} [Group G] [Finite G]

theorem card_sylow_of_equiv {Y : Type*} [Group Y] {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) {X A : Subgroup Y}
    (e : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hA : QuasithinUnique.IsSylowTwoOf A X) :
    Nat.card A = 2 ^ n := by
  have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    rw [← pow_mul]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have : Finite X := Finite.of_equiv _ e.toEquiv.symm
  have : Finite A := Finite.of_injective (Subgroup.inclusion hA.1) (Subgroup.inclusion_injective _)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hA.2.1
  have hcA : Nat.card (A.subgroupOf X) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  have hmul := Subgroup.index_mul_card (A.subgroupOf X)
  rw [hcA, ha, hX] at hmul
  have h1 : 2 ^ a ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := ⟨_, by rw [← hmul, mul_comm]⟩
  have h2 : 2 ^ n ∣ (A.subgroupOf X).index * 2 ^ a := ⟨_, hmul⟩
  have hcop1 : Nat.Coprime (2 ^ a) ((2 ^ n) ^ 2 - 1) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  have hidx : Odd (A.subgroupOf X).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hA.2.2)
  have hcop2 : Nat.Coprime (2 ^ n) (A.subgroupOf X).index :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hidx)
  have h3 : 2 ^ a ∣ 2 ^ n := hcop1.dvd_of_dvd_mul_right h1
  have h4 : 2 ^ n ∣ 2 ^ a := hcop2.dvd_of_dvd_mul_left h2
  rw [ha]
  exact Nat.dvd_antisymm h3 h4

omit [Finite G] in
theorem card_conjSubgroup (A : Subgroup G) (x : G) : Nat.card (conjSubgroup A x) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem card_vStar : Nat.card (autOn (fsuV T I) (VZ T H)) = 2 ^ n := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := d.kStar
  exact card_sylow_of_equiv (by have := d.c.two_le; omega) hF e d.sylow

theorem card_fsuV : Nat.card (fsuV T I) = 2 ^ n * Nat.card (bOf T I H) := by
  have hVN : fsuV T I ≤ Subgroup.normalizer (VZ T H : Set G) :=
    d.c.V_le_H.trans (SecC.le_normalizer_VZ T H)
  have h1 := Nat.card_congr (SecC.autOnEquiv (fsuV T I) (VZ T H) hVN).toEquiv
  rw [SecC.ker_autOnHom, d.card_vStar] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.centralizer (VZ T H : Set G)).subgroupOf (fsuV T I))
  rw [← h1] at h2
  rw [h2]
  congr 1
  rw [← Subgroup.inf_subgroupOf_left]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem Bh_le_normalizer_V (i : Inp32) :
    conjSubgroup (bOf T I H) h ≤ Subgroup.normalizer (fsuV T I : Set G) := fun x hx =>
  d.pCoreOf_le_normalizer_V ((d.Bh_eq i ▸ hx : x ∈ conjSubgroup (fsuV T I) h ⊓ pCoreOf 2 H).2)

theorem Bh_le_T (i : Inp32) : conjSubgroup (bOf T I H) h ≤ T := fun x hx =>
  d.pCoreOf_le_T ((d.Bh_eq i ▸ hx : x ∈ conjSubgroup (fsuV T I) h ⊓ pCoreOf 2 H).2)

theorem Bh_inf_centralizer_V (i : Inp32) :
    conjSubgroup (bOf T I H) h ⊓ Subgroup.centralizer (fsuV T I : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxC⟩
  have hxB : x ∈ bOf T I H := (d.P_inf_centralizer_V i).le ⟨Subgroup.mem_sup_right hx, hxC⟩
  have : x ∈ fsuV T I ⊓ conjSubgroup (fsuV T I) h :=
    ⟨(inf_le_left : bOf T I H ≤ fsuV T I) hxB, E3.conjSubgroup_mono_left _ inf_le_left hx⟩
  rwa [d.fsuV_inf_Vh i] at this

theorem card_autOn_Bh (i : Inp32) :
    Nat.card (autOn (conjSubgroup (bOf T I H) h) (fsuV T I)) = Nat.card (bOf T I H) := by
  rw [← card_conjSubgroup (bOf T I H) h]
  have h1 := Nat.card_congr (SecC.autOnEquiv _ (fsuV T I) (d.Bh_le_normalizer_V i)).toEquiv
  rw [SecC.ker_autOnHom] at h1
  have hker : (Subgroup.centralizer (fsuV T I : Set G)).subgroupOf
      (conjSubgroup (bOf T I H) h) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ conjSubgroup (bOf T I H) h ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [d.Bh_inf_centralizer_V i, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have h2 : Nat.card (autOn (conjSubgroup (bOf T I H) h) (fsuV T I)) =
      ((Subgroup.centralizer (fsuV T I : Set G)).subgroupOf (conjSubgroup (bOf T I H) h)).index :=
    h1
  rw [h2, hker, Subgroup.index_bot]

theorem autOn_Bh_le_normalizer (i : Inp32) : autOn (conjSubgroup (bOf T I H) h) (fsuV T I) ≤
    Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) := by
  rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
  exact conjAct_mem_normalizer_autOn hxN
    (d.c.s.hyp.normal (d.Bh_le_T i (Subgroup.mem_subgroupOf.mp hx)))

theorem autOn_Bh_sq : ∀ σ ∈ autOn (conjSubgroup (bOf T I H) h) (fsuV T I), σ * σ = 1 := by
  rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
  rw [← map_mul]
  have : (⟨x, hxN⟩ * ⟨x, hxN⟩ : ↥(Subgroup.normalizer (fsuV T I : Set G))) = 1 := by
    apply Subtype.ext
    show x * x = 1
    rw [← pow_two]
    exact d.sq_Bh (Subgroup.mem_subgroupOf.mp hx)
  rw [this, map_one]

theorem autOn_Bh_fix (i : Inp32) : ∀ σ ∈ autOn (conjSubgroup (bOf T I H) h) (fsuV T I),
    ∀ u ∈ (bOf T I H).subgroupOf (fsuV T I), σ u = u := by
  rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩ u hu
  apply Subtype.ext
  rw [conjAct_apply_coe]
  change x * u * x⁻¹ = u
  rw [← d.comm_B_Bh i (Subgroup.mem_subgroupOf.mp hu) (Subgroup.mem_subgroupOf.mp hx),
    mul_inv_cancel_right]

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
