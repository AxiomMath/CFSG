module

public import CFSG.Quasithin.Vol2.Ch11SecHFacts
public import CFSG.Quasithin.Vol2.Ch11SecC37N1
public import CFSG.Quasithin.Vol2.Ch11SecA13Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_top_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) {S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hS : IsPGroup 2 S) (hc : Nat.card S = 2 ^ n) : QuasithinUnique.IsSylowTwoOf S ⊤ := by
  refine ⟨le_top, hS, ?_⟩
  have h1 := Subgroup.index_mul_card S
  rw [hc, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF] at h1
  have h2 : S.index = (2 ^ n) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n) (by rw [h1, mul_comm])
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    rw [← pow_mul]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S, h2]
  exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem isSylowTwoOf_map_conj {X : Type*} [Group X] [Finite X] {S : Subgroup X}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (b : X) :
    QuasithinUnique.IsSylowTwoOf (S.map (MulAut.conj b).toMonoidHom) ⊤ := by
  refine ⟨le_top, hS.2.1.map _, ?_⟩
  have hc : Nat.card (S.map (MulAut.conj b).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj b).injective
  have h1 := Subgroup.index_mul_card S
  have h2 := Subgroup.index_mul_card (S.map (MulAut.conj b).toMonoidHom)
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h3 : (S.map (MulAut.conj b).toMonoidHom).index = S.index :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [← hc, h2, hc, h1])
  have h4 := hS.2.2
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h4
  rw [show ((S.map (MulAut.conj b).toMonoidHom).subgroupOf ⊤).index =
    (S.map (MulAut.conj b).toMonoidHom).index from Subgroup.relIndex_top_right _, h3]
  exact h4

theorem exists_relIndex_two_pow {N X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hX : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) ∈ N) :
    ∃ m : ℕ, N.relIndex X = 2 ^ m := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have hp : IsPGroup 2 (X ⧸ N.subgroupOf X) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hX x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hp
  exact ⟨m, hm⟩

theorem mem_normalizer_of_map_conj_eq {X : Type*} [Group X] {S : Subgroup X} {b : X}
    (h : S.map (MulAut.conj b).toMonoidHom = S) : b ∈ Subgroup.normalizer (S : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    rw [← h]
    exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
  · intro hs
    rw [← h] at hs
    obtain ⟨s', hs', hss'⟩ := hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hss'
    have : s' = s := by simpa using hss'
    exact this ▸ hs'

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G}

theorem exists_hall (s : SecC.Set37 T L I n V₁ H g) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6)
    (hKF5 : FactSL2TwoSylow) : ∃ D : Subgroup G,
      QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G)) := by
  obtain ⟨F, _, _, hF, φ, hφs, hφker⟩ := s.exists_phi h1135 h1136
  obtain ⟨hBtop, -⟩ := s.image_K_inf_M hF hφs hφker
  obtain ⟨hS2, hSc⟩ := s.card_image_T hF hφs
  have hn := s.two_le
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := s.hyp.normal
  have hSsyl := isSylowTwoOf_top_of_card (by omega) hF hS2 hSc
  have hSB : (T.subgroupOf (oTwoUpper H)).map φ ≤
      ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).map φ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hTM (Subgroup.mem_subgroupOf.mp hx))
  have hBN : ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).map φ ≤
      Subgroup.normalizer (((T.subgroupOf (oTwoUpper H)).map φ :
        Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) : Set _) := by
    intro b hb
    by_contra hbN
    have hne : (T.subgroupOf (oTwoUpper H)).map φ ≠
        ((T.subgroupOf (oTwoUpper H)).map φ).map (MulAut.conj b).toMonoidHom :=
      fun h => hbN (mem_normalizer_of_map_conj_eq h.symm)
    have hsup := hKF5 F n hn hF _ _ hSsyl (isSylowTwoOf_map_conj hSsyl b) hne
    apply hBtop
    rw [eq_top_iff, ← hsup]
    refine sup_le hSB ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb (hSB hx)) (Subgroup.inv_mem _ hb)
  have hX₀N : Subgroup.normalizer (L : Set G) ⊓ oTwoUpper H ≤
      Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := fun x hx =>
    s.mem_normalizer_of_image hφker (x := ⟨x, hx.2⟩)
      (hBN ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx.1, rfl⟩)
  have hTK := F7.isSylowTwoOf_inf_normal s.sylow hKH
    (s.h31.hstar.1.1.trans (le_normalizer_oTwoUpper H))
  have hTKle : T ⊓ oTwoUpper H ≤ Subgroup.normalizer (L : Set G) ⊓ oTwoUpper H :=
    inf_le_inf_right _ hTM
  have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ oTwoUpper H)
      (Subgroup.normalizer (L : Set G) ⊓ oTwoUpper H) := by
    refine ⟨hTKle, hTK.2.1, fun h2 => hTK.2.2 ?_⟩
    change 2 ∣ (T ⊓ oTwoUpper H).relIndex (oTwoUpper H)
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hTKle inf_le_right]
    exact h2.mul_right _
  obtain ⟨D, hD⟩ := SecA.exists_hall_of_normal_sylow' hsyl hX₀N
  have hX₀ : Subgroup.normalizer (L : Set G) ⊓ oTwoUpper H ≤
      H ⊓ Subgroup.normalizer (L : Set G) := le_inf (inf_le_right.trans hKH) inf_le_left
  obtain ⟨a, ha⟩ := hD.2.2
  have hpow : ∀ x ∈ H ⊓ Subgroup.normalizer (L : Set G), ∃ k : ℕ, x ^ (2 ^ k) ∈ oTwoUpper H :=
    fun x hx => two_of_sup s.hyp.fsu.sylow.1 (s.T_le.trans (le_normalizer_oTwoUpper H)) x
      (s.sup_eq.ge hx.1)
  obtain ⟨b, hb⟩ := exists_relIndex_two_pow
    (inf_le_left.trans (le_normalizer_oTwoUpper H)) hpow
  have hrel : (Subgroup.normalizer (L : Set G) ⊓ oTwoUpper H).relIndex
      (H ⊓ Subgroup.normalizer (L : Set G)) = (oTwoUpper H).relIndex
        (H ⊓ Subgroup.normalizer (L : Set G)) := by
    rw [← Subgroup.inf_relIndex_right (oTwoUpper H)]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.2, hKH h.2, h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩
  refine ⟨D, hD.1.trans hX₀, hD.2.1, a + b, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hD.1 hX₀, ha, hrel, hb, pow_add]

end CFSG.Quasithin.Vol2.Ch11.SecH
