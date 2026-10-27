module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5T
public import CFSG.Quasithin.EmptyFaithful.S152He9Y2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Cyclic

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_le_isCyclic {D E : Subgroup G} (hD : IsCyclic ↥D) (hED : E ≤ D)
    {g : G} (hgD : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer (E : Set G) := by
  have := hD
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ D := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hgD]
    exact Subgroup.map_mono hED
  have hcard : Nat.card ((E.map (MulAut.conj g).toMonoidHom).subgroupOf D) =
      Nat.card (E.subgroupOf D) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h := (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hle, inf_eq_left.mpr hED] at h
  exact h

theorem mem_normalizer_sup_of_isCyclic {P D E Bo : Subgroup G} (hPB : P ≤ Bo)
    (hBP : Bo ≤ Subgroup.normalizer (P : Set G)) (hDP : D ⊔ P = Bo) (hD : IsCyclic ↥D)
    (hED : E ≤ D) {g : G} (hgB : g ∈ Subgroup.normalizer (Bo : Set G))
    (hgP : g ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer ((P ⊔ E : Subgroup G) : Set G) := by
  have hDB : D ≤ Bo := hDP ▸ le_sup_left
  set N : Subgroup ↥Bo := P.subgroupOf Bo with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPB).mpr hBP
  set π := QuotientGroup.mk' N with hπ
  have hcyc : IsCyclic (↥Bo ⧸ N) := by
    have := hD
    refine isCyclic_of_surjective (π.comp (Subgroup.inclusion hDB)) ?_
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hb : (b : G) ∈ ((D ⊔ P : Subgroup G) : Set G) := by rw [hDP]; exact b.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D P (hDB.trans hBP)] at hb
    obtain ⟨d, hd, p, hp, hdp⟩ := hb
    refine ⟨⟨d, hd⟩, ?_⟩
    show π ⟨d, hDB hd⟩ = π b
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (⟨d, hDB hd⟩ : ↥Bo)⁻¹ * b = ⟨p, hPB hp⟩ := Subtype.ext (by simp [← hdp])
    rw [e]
    exact hp
  set Z := P ⊔ E with hZ
  have hEB : E ≤ Bo := hED.trans hDB
  have hZB : Z ≤ Bo := sup_le hPB hEB
  set Z' := Z.map (MulAut.conj g).toMonoidHom with hZ'
  have hZ'B : Z' ≤ Bo := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hgB]
    exact Subgroup.map_mono hZB
  have hPZ' : P ≤ Z' := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hgP]
    exact Subgroup.map_mono le_sup_left
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hcomap : ∀ W : Subgroup G, P ≤ W →
      ((W.subgroupOf Bo).map π).comap π = W.subgroupOf Bo := by
    intro W hPW
    rw [Subgroup.comap_map_eq, hker, sup_eq_left]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hPW (Subgroup.mem_subgroupOf.mp hx))
  have hidx : ∀ W : Subgroup G, P ≤ W →
      ((W.subgroupOf Bo).map π).index = (W.subgroupOf Bo).index := by
    intro W hPW
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), hcomap W hPW]
  have hcardZ : Nat.card (Z'.subgroupOf Bo) = Nat.card (Z.subgroupOf Bo) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ'B).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv, hZ',
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hindex : (Z'.subgroupOf Bo).index = (Z.subgroupOf Bo).index := by
    have h1 := (Z'.subgroupOf Bo).card_mul_index
    have h2 := (Z.subgroupOf Bo).card_mul_index
    rw [hcardZ] at h1
    have hpos : 0 < Nat.card (Z.subgroupOf Bo) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have heq : (Z'.subgroupOf Bo).map π = (Z.subgroupOf Bo).map π :=
    (IsCyclic.subgroup_eq_iff_index_eq).mpr
      (by rw [hidx Z' hPZ', hidx Z le_sup_left, hindex])
  have h2 : Z'.subgroupOf Bo = Z.subgroupOf Bo := by
    rw [← hcomap Z' hPZ', heq, hcomap Z le_sup_left]
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hZ'B, inf_eq_left.mpr hZB] at h2
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

end Cyclic

section Setting

variable {G : Type} [Group G]

@[expose] def z518 (T L D₅ : Subgroup G) : Subgroup G := (T ⊓ L) ⊔ D₅

namespace Setting518D5

variable [Finite G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem isCyclic_D (hF : L2TorusFact) : IsCyclic ↥D :=
  (s.hyp.hyp.toHyp5_0_1.isCyclic_card_of_isHall hF s.hyp.notation59.2.1).1

theorem D₅_le_borel : D₅ ≤ borelL T L := s.D₅_le.trans s.hyp.notation59.2.1.1

theorem D₅_inf_eq_bot {P : Subgroup G} (hP : IsPGroup 2 P) : D₅ ⊓ P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
  rw [hm, s.card_D₅]
  exact Nat.Coprime.pow_right m (by norm_num)

theorem T_le_normalizer_z518 (hF : L2TorusFact) :
    T ≤ Subgroup.normalizer (z518 T L D₅ : Set G) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  have hTL := hh.T_le_normalizer_inf
  have hTLN : T ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans hh.sup_le_normalizer
  intro t ht
  have hNN : t ∈ Subgroup.normalizer
      (Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)).map
      (MulAut.conj t).toMonoidHom = _
    rw [Subgroup.map_equiv_normalizer_eq]
    congr 1
    exact congrArg (fun A : Subgroup G => (A : Set G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTL ht))
  have hB : t ∈ Subgroup.normalizer (borelL T L : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTLN ht, hNN⟩
  exact mem_normalizer_sup_of_isCyclic (le_inf inf_le_right Subgroup.le_normalizer) inf_le_right
    (hh.borelL_eq_sup s.hyp.notation59.2.1) (s.isCyclic_D hF) s.D₅_le hB (hTL ht)

theorem D₅_le_normalizer_inf : D₅ ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
  s.D₅_le_borel.trans inf_le_right

theorem B_le_normalizer_z518 (hF : L2TorusFact) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    B ≤ Subgroup.normalizer (z518 T L D₅ : Set G) := by
  have hBL : B ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans
      (s.hyp.DBT_le_normalizer_inf_L_of_le h331 hR (d518_le H D))
  have hBD : B ≤ Subgroup.normalizer (D₅ : Set G) := fun b hb =>
    mem_normalizer_of_le_isCyclic (s.isCyclic_D hF) s.D₅_le (s.hyp.notation59.2.2 hb)
  exact le_normalizer_sup_of_le hBL hBD

theorem relIndex_z518 : (T ⊓ L).relIndex (z518 T L D₅) = 5 := by
  have hh := s.hyp.hyp.toHyp5_0_1
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' s.D₅_le_normalizer_inf
  rw [sup_comm] at h1
  rw [z518, h1, ← Subgroup.inf_relIndex_right, inf_comm,
    s.D₅_inf_eq_bot (hh.sylow.1.to_le inf_le_left), Subgroup.relIndex_bot_left, s.card_D₅]

theorem pCoreOf_z518 : pCoreOf 2 (z518 T L D₅) = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hT2 : IsPGroup 2 ↥(T ⊓ L : Subgroup G) := hh.sylow.1.to_le inf_le_left
  have hZN : z518 T L D₅ ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer s.D₅_le_normalizer_inf
  have hsyl : IsSylowTwoOf (T ⊓ L) (z518 T L D₅) :=
    ⟨le_sup_left, hT2, by
      show ¬ 2 ∣ (T ⊓ L).relIndex (z518 T L D₅)
      rw [s.relIndex_z518]
      norm_num⟩
  exact le_antisymm (F7.isSylowTwoOf_pCoreOf_le hsyl)
    (le_pCoreOf_of_le_normalizer 2 le_sup_left hZN hT2)

theorem D₅_not_le_normalizer_S (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first)
    (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    ¬ D₅ ≤ Subgroup.normalizer (s518 T H B D : Set G) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨hST, -, hTKS, hOMS, -, hSN⟩ := s.S_facts h510 h331 hR
  have hS1 : s518 T H B D ≠ ⊥ := by
    intro h0
    apply pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1
    exact le_bot_iff.mp (h0 ▸ hOMS)
  have hNS := s.normalizer_le_Mp h311 h5114 hS1 hST hTKS (le_sup_right.trans hSN)
  exact fun h => s.D₅_not_le (h.trans hNS)

@[expose] def sd5 (T L H B D D₅ : Subgroup G) : Subgroup G := z518 T L D₅ ⊔ s518 T H B D

theorem sd5_facts (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first)
    (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    IsSylowTwoOf (s518 T H B D) (sd5 T L H B D D₅) ∧
      (s518 T H B D).relIndex (sd5 T L H B D D₅) = 5 ∧
      (Nonempty (OTwoQuot (sd5 T L H B D D₅) ≃* DihedralGroup 5) ∨
        Nonempty (OTwoQuot (sd5 T L H B D D₅) ≃* ↥(CFSG.Open.Sz 0))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hST, hTLS, -, -, -, -⟩ := s.S_facts h510 h331 hR
  have hS2 : IsPGroup 2 (s518 T H B D) := pCoreOf_isPGroup 2 _
  have hSZ : s518 T H B D ≤ Subgroup.normalizer (z518 T L D₅ : Set G) :=
    hST.trans (s.T_le_normalizer_z518 hF)
  have hO := s.pCoreOf_z518
  refine He9.oTwoQuot_sup_iso hS2 hSZ (by rw [hO]; exact s.relIndex_z518)
    (by rw [hO]; exact hTLS) ?_
  by_contra hcon
  push Not at hcon
  apply s.D₅_not_le_normalizer_S h311 h5114 h510 h331 hR
  intro d hd
  have hdZ : d ∈ z518 T L D₅ := Subgroup.mem_sup_right hd
  have hconj : ∀ d ∈ z518 T L D₅, ∀ x ∈ s518 T H B D, d * x * d⁻¹ ∈ s518 T H B D := by
    intro d hd x hx
    have h1 : x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ ∈ s518 T H B D := by
      have := hcon x⁻¹ ((s518 T H B D).inv_mem hx) d hd
      rw [hO] at this
      exact hTLS this
    have h2 := (s518 T H B D).mul_mem hx h1
    simpa [mul_assoc] using h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj d hdZ x hx, fun hx => ?_⟩
  have := hconj d⁻¹ ((z518 T L D₅).inv_mem hdZ) _ hx
  simpa [mul_assoc] using this

theorem borelOf_sd5 (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first)
    (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    borelOf (sd5 T L H B D D₅) (s518 T H B D) = s518 T H B D := by
  obtain ⟨-, hidx, -⟩ := s.sd5_facts hF h311 h5114 h510 h331 hR
  have hSY : s518 T H B D ≤ sd5 T L H B D D₅ := le_sup_right
  have hinf : s518 T H B D ⊓ sd5 T L H B D D₅ = s518 T H B D := inf_eq_left.mpr hSY
  unfold borelOf
  rw [hinf]
  set Nn := sd5 T L H B D D₅ ⊓ Subgroup.normalizer (s518 T H B D : Set G) with hNn
  have hSN : s518 T H B D ≤ Nn := le_inf hSY Subgroup.le_normalizer
  have hNY : Nn ≤ sd5 T L H B D D₅ := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hSN hNY
  rw [hidx] at hmul
  have hdvd : (s518 T H B D).relIndex Nn ∣ 5 := Dvd.intro _ hmul
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSN
  · exfalso
    rw [h5] at hmul
    have h1 : Nn.relIndex (sd5 T L H B D D₅) = 1 := by omega
    have hYN := Subgroup.relIndex_eq_one.mp h1
    apply s.D₅_not_le_normalizer_S h311 h5114 h510 h331 hR
    exact ((le_sup_right.trans le_sup_left : D₅ ≤ sd5 T L H B D D₅).trans hYN).trans
      inf_le_right

end Setting518D5

end Setting

end CFSG.Quasithin.H13
