module

public import CFSG.Quasithin.Recognition.St84.Gen.CrossedHomSecRep
public import CFSG.Quasithin.Background.SpecialPowCenter
public import CFSG.Quasithin.Recognition.St84.Gen.D4qVertexOneDefs
public import CFSG.Quasithin.Recognition.St84.Gen.TriH1
public import CFSG.Quasithin.Recognition.St84.Gen.TriModule
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQSL2RootCommutator
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin.H13.NFa2 CFSG.Quasithin.JonesParshall CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {Q Z K H : Subgroup G} {f : ℕ}

private theorem special_center_facts {Q : Subgroup G} {q w : ℕ} (hq : 2 ≤ q) (hw : 1 ≤ w)
    (h : IsSpecialPow 2 q w ↥Q) :
    frattini ↥Q = Subgroup.center ↥Q ∧ commutator ↥Q = Subgroup.center ↥Q ∧
      ∀ z ∈ Subgroup.center ↥Q, z ^ 2 = 1 := by
  obtain ⟨⟨hP, hs⟩, hcard, hcen⟩ := h
  rcases hs with ⟨hcomm, hpow⟩ | ⟨hc, hf, hz⟩
  · exfalso
    have htop : Subgroup.center ↥Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subgroup.mem_center_iff.mpr fun g => hcomm.is_comm.comm g x
    rw [htop, Subgroup.card_top, hcard] at hcen
    have hlt : q < q ^ (1 + 2 * w) := by
      calc q = q ^ 1 := (pow_one q).symm
        _ < q ^ (1 + 2 * w) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  · exact ⟨hf, hc, hz⟩

private theorem one_le_f_of_data (hd : D4qVertexOneData Q Z K H f) : 1 ≤ f := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [hd.card_torus] at hpos
  rcases Nat.eq_zero_or_pos f with hf0 | hf
  · rw [hf0] at hpos
    norm_num at hpos
  · exact hf

private theorem two_le_two_pow_of_data (hd : D4qVertexOneData Q Z K H f) : 2 ≤ 2 ^ f := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (one_le_f_of_data hd)

theorem D4qVertexOneData.le (hd : D4qVertexOneData Q Z K H f) : Z ≤ Q := by
  rw [← hd.centerOf_eq]
  exact inf_le_left

theorem D4qVertexOneData.commute_of_mem (hd : D4qVertexOneData Q Z K H f) :
    ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z := by
  intro z hz x hx
  have hz' : z ∈ centerOf Q := by rwa [hd.centerOf_eq]
  exact (Subgroup.mem_centralizer_iff.mp hz'.2 x hx).symm

theorem D4qVertexOneData.sq_eq_one (hd : D4qVertexOneData Q Z K H f) :
    ∀ z ∈ Z, z ^ 2 = 1 := by
  intro z hz
  have hz' : z ∈ centerOf Q := by rwa [hd.centerOf_eq]
  have hmap : z ∈ (Subgroup.center ↥Q).map Q.subtype := by
    rwa [← CFSG.Quasithin.A1c.centerOf_eq_map_center]
  obtain ⟨y, hy, rfl⟩ := hmap
  have h := (special_center_facts (two_le_two_pow_of_data hd) (by norm_num) hd.special).2.2 y hy
  simpa using congrArg Subtype.val h

theorem D4qVertexOneData.sq_mem (hd : D4qVertexOneData Q Z K H f) :
    ∀ x ∈ Q, x ^ 2 ∈ Z := by
  intro x hx
  have hfr := (special_center_facts (two_le_two_pow_of_data hd) (by norm_num) hd.special).1
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hd.special.1.1⟩
  have hmem : (⟨x, hx⟩ : ↥Q) ^ 2 ∈ Subgroup.center ↥Q := by
    rw [← hfr]
    exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) _
  have hmem' : x ^ 2 ∈ centerOf Q := by
    rw [CFSG.Quasithin.A1c.centerOf_eq_map_center]
    exact Subgroup.mem_map.mpr ⟨_, hmem, by simp⟩
  rwa [hd.centerOf_eq] at hmem'

theorem D4qVertexOneData.commutator_mem (hd : D4qVertexOneData Q Z K H f) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  have hcomm := (CFSG.Quasithin.H13.commutator_eq_centerOf_of_isSpecialPow
    (p := 2) (q := 2 ^ f) (w := 4) (by norm_num) (two_le_two_pow_of_data hd) hd.special).1
  intro x hx y hy
  have hmem : ⁅x, y⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm, hd.centerOf_eq] at hmem
  simpa [commutatorElement_def] using hmem

theorem D4qVertexOneData.card_center (hd : D4qVertexOneData Q Z K H f) :
    Nat.card Z = 2 ^ f := by
  have h := (CFSG.Quasithin.H13.commutator_eq_centerOf_of_isSpecialPow
    (p := 2) (q := 2 ^ f) (w := 4) (by norm_num) (two_le_two_pow_of_data hd) hd.special).2
  rwa [hd.centerOf_eq] at h

theorem D4qVertexOneData.card (hd : D4qVertexOneData Q Z K H f) :
    Nat.card Q = 2 ^ (9 * f) := by
  rw [hd.special.2.1, ← pow_mul]
  congr 1
  ring

theorem D4qVertexOneData.le_normalizer (hd : D4qVertexOneData Q Z K H f) :
    K ⊔ H ≤ Subgroup.normalizer (Q : Set G) :=
  sup_le hd.levi_le_normalizer hd.torus_le_normalizer

theorem D4qVertexOneData.conj_mem_center (hd : D4qVertexOneData Q Z K H f) :
    ∀ r ∈ K ⊔ H, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z := by
  intro r hr z hz
  have hN : r ∈ Subgroup.normalizer (centerOf Q : Set G) :=
    CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf Q (hd.le_normalizer hr)
  have hz' : z ∈ centerOf Q := by rwa [hd.centerOf_eq]
  have h := (Subgroup.mem_normalizer_iff.mp hN z).mp hz'
  rwa [hd.centerOf_eq] at h

theorem D4qVertexOneData.conj_mem_levi (hd : D4qVertexOneData Q Z K H f) :
    ∀ r ∈ K ⊔ H, ∀ k ∈ K, r * k * r⁻¹ ∈ K := by
  have hHc : H ≤ Subgroup.centralizer (K : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact hd.levi_commute_torus k hk h hh
  have hH : H ≤ Subgroup.normalizer (K : Set G) :=
    hHc.trans (Subgroup.centralizer_le_normalizer (K : Set G))
  have hNK : K ⊔ H ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hH
  intro r hr k hk
  exact (Subgroup.mem_normalizer_iff.mp (hNK hr) k).mp hk

theorem D4qVertexOneData.secHyp (hd : D4qVertexOneData Q Z K H f) :
    CFSG.Quasithin.H13.NFa2.SecHyp (K ⊔ H) Z Q where
  le := hd.le
  norm₀ := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hd.conj_mem_center r hr z hz, fun hz => ?_⟩
    have h := hd.conj_mem_center r⁻¹ ((K ⊔ H).inv_mem hr) (r * z * r⁻¹) hz
    have hEq : z = r⁻¹ * (r * z * r⁻¹) * r := by group
    rw [hEq]
    simpa using h
  norm₁ := hd.le_normalizer
  normal := by
    have hZc : Z ≤ Subgroup.centralizer (Q : Set G) := by
      rw [← hd.centerOf_eq]
      exact inf_le_right
    have hQc : Q ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZc
    exact hQc.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
  comm := hd.commutator_mem
  sq := fun a ha => by simpa [pow_two] using hd.sq_mem a ha

theorem D4qVertexOneData.isChiefPair (hd : D4qVertexOneData Q Z K H f) :
    CFSG.Quasithin.H13.NFa2.IsChiefPair K Z Q where
  lt := by
    have hf1 : 1 ≤ f := one_le_f_of_data hd
    refine lt_of_le_of_ne hd.le ?_
    intro hEq
    have hcard : Nat.card Z = Nat.card Q := by rw [hEq]
    rw [hd.card_center, hd.card] at hcard
    have hlt : 2 ^ f < 2 ^ (9 * f) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact (ne_of_lt hlt) hcard
  norm₀ := le_sup_left.trans hd.secHyp.norm₀
  norm₁ := le_sup_left.trans hd.secHyp.norm₁
  normal := hd.secHyp.normal
  min := fun N hZN hNQ hKN => hd.irreducible N hZN hNQ hKN

private def secRepRestrict {R K N₀ N₁ : Subgroup G} (hKR : K ≤ R) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (s : SecRep R N₀ N₁ W) : SecRep K N₀ N₁ W where
  ρ := s.ρ.comp (Subgroup.inclusion hKR)
  cls := s.cls
  surj := s.surj
  ker := s.ker
  act := fun x n m hm => s.act (Subgroup.inclusion hKR x) n m hm

private theorem secHyp_of_le {R K N₀ N₁ : Subgroup G} (hKR : K ≤ R) (h : SecHyp R N₀ N₁) :
    SecHyp K N₀ N₁ where
  le := h.le
  norm₀ := hKR.trans h.norm₀
  norm₁ := hKR.trans h.norm₁
  normal := h.normal
  comm := h.comm
  sq := h.sq

@[expose] def leviRep {R K : Subgroup G} (hKR : K ≤ R) {N₀ N₁ : Subgroup G} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W]
    (s : CFSG.Quasithin.H13.NFa2.SecRep R N₀ N₁ W) : Representation (ZMod 2) ↥K W where
  toFun k := (s.ρ (Subgroup.inclusion hKR k) : W →ₗ[ZMod 2] W)
  map_one' := by
    ext w
    simp
  map_mul' k l := by
    ext w
    simp [map_mul]

theorem leviRep_apply {R K : Subgroup G} (hKR : K ≤ R) {N₀ N₁ : Subgroup G} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W]
    (s : CFSG.Quasithin.H13.NFa2.SecRep R N₀ N₁ W) (k : ↥K) (w : W) :
    leviRep hKR s k w = s.ρ (Subgroup.inclusion hKR k) w := rfl

theorem D4qVertexOneData.card_secRep (hd : D4qVertexOneData Q Z K H f) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : CFSG.Quasithin.H13.NFa2.SecRep (K ⊔ H) Z Q W) :
    Nat.card W = 2 ^ (8 * f) := by
  classical
  have hkereq : s.cls.ker = Z.subgroupOf Q := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact s.ker n
  have hquot : Nat.card (↥Q ⧸ Z.subgroupOf Q) = Nat.card W := by
    rw [← hkereq]
    calc Nat.card (↥Q ⧸ s.cls.ker) = Nat.card ↥s.cls.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange s.cls).toEquiv
      _ = Nat.card (⊤ : Subgroup (Multiplicative W)) := by
          rw [MonoidHom.range_eq_top.mpr s.surj]
      _ = Nat.card (Multiplicative W) :=
          Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = Nat.card W := Nat.card_congr Multiplicative.toAdd
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf Q)
  have hsub : Nat.card ↥(Z.subgroupOf Q) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hd.le).toEquiv
  rw [hquot, hsub, hd.card, hd.card_center] at hcard
  have hpow : 2 ^ (9 * f) = 2 ^ (8 * f) * 2 ^ f := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow] at hcard
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by norm_num)) hcard).symm

theorem D4qVertexOneData.exists_leviRep_ne_one (hf : 2 ≤ f)
    (hd : D4qVertexOneData Q Z K H f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (s : CFSG.Quasithin.H13.NFa2.SecRep (K ⊔ H) Z Q W) :
    ∃ k, leviRep le_sup_left s k ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hcard : Nat.card W = 2 ^ (8 * f) := hd.card_secRep s
  have hnt : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    haveI : Subsingleton W := hW
    have hcard1 : Nat.card W = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩
    rw [hcard] at hcard1
    have hlt : 1 < 2 ^ (8 * f) := by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (8 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨w, hw0⟩ := exists_ne (0 : W)
  let U : Submodule (ZMod 2) W := Submodule.span (ZMod 2) {w}
  have hwU : w ∈ U := Submodule.subset_span (Set.mem_singleton w)
  have hUfin : Module.finrank (ZMod 2) U = 1 := by
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {w}) = 1
    rw [finrank_span_singleton hw0]
  have hWfin : Module.finrank (ZMod 2) W = 8 * f := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hcard, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective (by norm_num) h1).symm
  have hUbot : U ≠ ⊥ := by
    intro hbot
    have hw : w ∈ (⊥ : Submodule (ZMod 2) W) := by rw [← hbot]; exact hwU
    exact hw0 ((Submodule.mem_bot (R := ZMod 2)).mp hw)
  have hUtop : U ≠ ⊤ := by
    intro htop
    have hfr : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) W := by
      rw [htop, finrank_top]
    rw [hUfin, hWfin] at hfr
    omega
  let sK : SecRep K Z Q W := secRepRestrict le_sup_left s
  let hK : SecHyp K Z Q := secHyp_of_le le_sup_left hd.secHyp
  have hUinv : ∀ k : ↥K, ∀ u ∈ U, sK.ρ k u ∈ U := by
    intro k u hu
    have hk' : (s.ρ (Subgroup.inclusion le_sup_left k) : W →ₗ[ZMod 2] W) = 1 := by
      simpa [leviRep] using h k
    change ((s.ρ (Subgroup.inclusion le_sup_left k) : W →ₗ[ZMod 2] W) u) ∈ U
    rw [hk']
    exact hu
  rcases SecRep.irreducible hd.isChiefPair hK sK U hUinv with hbot | htop
  · exact hUbot hbot
  · exact hUtop htop

theorem D4qVertexOneData.isIrreducible_leviRep (hf : 2 ≤ f)
    (hd : D4qVertexOneData Q Z K H f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (s : CFSG.Quasithin.H13.NFa2.SecRep (K ⊔ H) Z Q W) :
    (leviRep le_sup_left s).IsIrreducible := by
  classical
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI : Subsingleton W := h
    obtain ⟨k, hk⟩ := hd.exists_leviRep_ne_one hf s
    exact hk (Subsingleton.elim _ _)
  · intro U hU
    let sK : SecRep K Z Q W := secRepRestrict le_sup_left s
    let hK : SecHyp K Z Q := secHyp_of_le le_sup_left hd.secHyp
    have hU' : ∀ k : ↥K, ∀ u ∈ U, sK.ρ k u ∈ U := fun k u hu => hU k u hu
    exact SecRep.irreducible hd.isChiefPair hK sK U hU'

noncomputable def D4qVertexOneData.leviRepSL {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (hd : D4qVertexOneData Q Z K H f) (s : SecRep (K ⊔ H) Z Q W) :
    Representation (ZMod 2) (SL(2, GaloisField 2 (3 * f))) W :=
  (leviRep le_sup_left s).comp hd.levi_mulEquiv.some.symm.toMonoidHom

theorem D4qVertexOneData.leviRepSL_apply {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (hd : D4qVertexOneData Q Z K H f) (s : SecRep (K ⊔ H) Z Q W) (k : ↥K) :
    hd.leviRepSL s (hd.levi_mulEquiv.some k) = leviRep le_sup_left s k := by
  simp [D4qVertexOneData.leviRepSL]

theorem D4qVertexOneData.isIrreducible_leviRepSL (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : SecRep (K ⊔ H) Z Q W) : (hd.leviRepSL s).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  obtain ⟨hnt, hinv⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff
    (leviRep le_sup_left s)).mp (hd.isIrreducible_leviRep hf s)
  refine ⟨hnt, fun U hU => hinv U ?_⟩
  intro k u hu
  rw [← hd.leviRepSL_apply s k]
  exact hU (hd.levi_mulEquiv.some k) u hu

theorem D4qVertexOneData.exists_leviRepSL_ne_one (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : SecRep (K ⊔ H) Z Q W) : ∃ g, hd.leviRepSL s g ≠ 1 := by
  obtain ⟨k, hk⟩ := hd.exists_leviRep_ne_one hf s
  refine ⟨hd.levi_mulEquiv.some k, fun h => hk ?_⟩
  rwa [hd.leviRepSL_apply s k] at h

theorem D4qVertexOneData.card_endRing_leviRep (hf : 2 ≤ f)
    (hd : D4qVertexOneData Q Z K H f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (s : SecRep (K ⊔ H) Z Q W) :
    Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing (leviRep le_sup_left s)) = 2 ^ f := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 (3 * f)) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 (3 * f)) = 2 ^ (3 * f) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (3 * f) (by omega)
  haveI : Fact (hd.leviRepSL s).IsIrreducible :=
    ⟨hd.isIrreducible_leviRepSL hf s⟩
  have hnt := hd.exists_leviRepSL_ne_one hf s
  have hW : Nat.card W = 2 ^ (8 * f) := hd.card_secRep s
  have hcardSL : Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (hd.leviRepSL s)) = 2 ^ f :=
    card_endRing_eq_of_card_eq_two_pow_eight_mul (by omega : 1 ≤ f) hF
      (hd.leviRepSL s) hnt hW
  rw [← hcardSL]
  congr 1
  have hrange : Set.range (hd.leviRepSL s) =
      Set.range (leviRep le_sup_left s) := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨hd.levi_mulEquiv.some.symm g, by simp [D4qVertexOneData.leviRepSL]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨hd.levi_mulEquiv.some k, by simp [D4qVertexOneData.leviRepSL]⟩
  show CFSG.QuasithinUnique.Setup.SL2Modules.EndRing (leviRep le_sup_left s) =
      CFSG.QuasithinUnique.Setup.SL2Modules.EndRing (hd.leviRepSL s)
  show Module.End (CFSG.QuasithinUnique.Setup.SL2Modules.spanAlg
        (leviRep le_sup_left s)) W =
      Module.End (CFSG.QuasithinUnique.Setup.SL2Modules.spanAlg
        (hd.leviRepSL s)) W
  rw [show CFSG.QuasithinUnique.Setup.SL2Modules.spanAlg (leviRep le_sup_left s) =
      CFSG.QuasithinUnique.Setup.SL2Modules.spanAlg
        (hd.leviRepSL s) from by
    show Algebra.adjoin (ZMod 2) (Set.range (leviRep le_sup_left s)) =
      Algebra.adjoin (ZMod 2) (Set.range (hd.leviRepSL s))
    rw [hrange]]

theorem D4qVertexOneData.mem_B1_leviRep (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : CFSG.Quasithin.H13.NFa2.SecRep (K ⊔ H) Z Q W) :
    ∀ φ : ↥K → W, φ ∈ Z1 (leviRep le_sup_left s) → φ ∈ B1 (leviRep le_sup_left s) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 (3 * f)) := Fintype.ofFinite _
  haveI : Fact (hd.leviRepSL s).IsIrreducible :=
    ⟨hd.isIrreducible_leviRepSL hf s⟩
  have hnt := hd.exists_leviRepSL_ne_one hf s
  have hF : Fintype.card (GaloisField 2 (3 * f)) = 2 ^ (3 * f) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (3 * f) (by omega)
  have hW : Nat.card W = 2 ^ (8 * f) := hd.card_secRep s
  obtain ⟨K', hK'field, hK'fin, hK'alg, hK'card, σ, β, hβ⟩ :=
    exists_kForm_model hf hF (hd.leviRepSL s) hnt hW
  letI : Field K' := hK'field
  letI : Fintype K' := hK'fin
  letI : Algebra K' (GaloisField 2 (3 * f)) := hK'alg
  let τ : GaloisField 2 (3 * f) →ₐ[K'] GaloisField 2 (3 * f) :=
    FiniteField.frobeniusAlgHom K' (GaloisField 2 (3 * f))
  have hτ : ∀ a, τ a = a ^ 2 ^ f := by
    intro a
    rw [show τ a = (FiniteField.frobeniusAlgHom K' (GaloisField 2 (3 * f))) a from rfl,
      FiniteField.frobeniusAlgHom_apply, hK'card]
  have hτ3 : ∀ a, τ (τ (τ a)) = a := by
    intro a
    have hexp : 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card (GaloisField 2 (3 * f)) := by
      rw [hF, ← pow_add, ← pow_add]
      congr 1
      ring
    have hpow : τ (τ (τ a)) = a ^ (2 ^ f * (2 ^ f * 2 ^ f)) := by
      simp only [hτ, pow_mul]
    rw [hpow, hexp]
    exact FiniteField.pow_card a
  have hβ' : ∀ (γ : ↥K) (w : W), β (leviRep le_sup_left s γ w) =
      kFormAct τ hτ3 (D2.slMap σ (hd.levi_mulEquiv.some γ)) (β w) := by
    intro γ w
    have h := hβ (hd.levi_mulEquiv.some γ) w
    rw [hd.leviRepSL_apply s γ] at h
    apply Subtype.ext
    simpa [kFormAct_apply] using h
  intro φ hφ
  exact mem_B1_of_kFormAct hf hF τ hτ hτ3 (leviRep le_sup_left s)
    hd.levi_mulEquiv.some σ β hβ' hφ

theorem D4qVertexOneData.exists_invariant_form (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : CFSG.Quasithin.H13.NFa2.SecRep (K ⊔ H) Z Q W) :
    ∃ B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2,
      (∀ k x y, B (leviRep le_sup_left s k x) (leviRep le_sup_left s k y) = B x y) ∧
      ∀ x, (∀ y, B x y = 0) → x = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 (3 * f)) := Fintype.ofFinite _
  haveI : Fact (hd.leviRepSL s).IsIrreducible :=
    ⟨hd.isIrreducible_leviRepSL hf s⟩
  have hnt := hd.exists_leviRepSL_ne_one hf s
  have hF : Fintype.card (GaloisField 2 (3 * f)) = 2 ^ (3 * f) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (3 * f) (by omega)
  have hW : Nat.card W = 2 ^ (8 * f) := hd.card_secRep s
  let ρD : Representation (ZMod 2) (SL(2, GaloisField 2 (3 * f)))
      (Module.Dual (ZMod 2) W) := (hd.leviRepSL s).dual
  haveI : Fact ρD.IsIrreducible :=
    ⟨CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ.isIrreducible_dual _ Fact.out⟩
  haveI : Finite (Module.Dual (ZMod 2) W) := Module.finite_of_finite (ZMod 2)
  have hWdual : Nat.card (Module.Dual (ZMod 2) W) = 2 ^ (8 * f) := by
    rw [natCard_dual_eq, hW]
  have hntD : ∃ g, ρD g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g⁻¹, fun hcon => hg ?_⟩
    ext x
    have hfix : ∀ f : Module.Dual (ZMod 2) W, f ((hd.leviRepSL s) g x) = f x := by
      intro f
      have h1 : ρD g⁻¹ f = f := by
        rw [hcon]
        rfl
      have h2 := congrArg (fun T : Module.Dual (ZMod 2) W => T x) h1
      rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply] at h2
      simpa using h2
    have hzero : (hd.leviRepSL s) g x - x = 0 := by
      refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp fun f => ?_
      rw [map_sub, hfix f, sub_self]
    exact sub_eq_zero.mp hzero
  obtain ⟨e, he⟩ := exists_equiv_of_card_eq_two_pow_eight_mul hf hF
    (hd.leviRepSL s) ρD hnt hntD hW hWdual
  refine ⟨e.toLinearMap, ?_, ?_⟩
  · intro k x y
    calc e (leviRep le_sup_left s k x) (leviRep le_sup_left s k y)
        = e ((hd.leviRepSL s) (hd.levi_mulEquiv.some k) x)
            ((hd.leviRepSL s) (hd.levi_mulEquiv.some k) y) := by
          rw [hd.leviRepSL_apply s k]
      _ = (ρD (hd.levi_mulEquiv.some k) (e x))
            ((hd.leviRepSL s) (hd.levi_mulEquiv.some k) y) := by rw [he]
      _ = (ρD (hd.levi_mulEquiv.some k) (e x)) (leviRep le_sup_left s k y) := by
          rw [hd.leviRepSL_apply s k]
      _ = e x y := by
          rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
          congr 1
          have hsym : ((hd.leviRepSL s) ((hd.levi_mulEquiv.some k)⁻¹))
              (((hd.leviRepSL s) (hd.levi_mulEquiv.some k)) y) = y := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl
          simpa [hd.leviRepSL_apply s k] using hsym
      _ = e x y := rfl
  · intro x hx
    apply e.injective
    apply LinearMap.ext
    intro y
    rw [map_zero]
    exact hx y

theorem D4qVertexOneData.crossedHomPrincipal (hf : 2 ≤ f)
    (hd : D4qVertexOneData Q Z K H f) {G' : Type} [Group G'] [Finite G']
    {Z' R' : Subgroup G'} (e : ↥(K ⊔ H) ≃* ↥R')
    (hR'Z' : ∀ r ∈ R', ∀ z ∈ Z', r * z * r⁻¹ ∈ Z')
    (hZ'c : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a)
    (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1)
    (hKZ' : ∀ k : ↥(K ⊔ H), (k : G) ∈ K → ∀ z ∈ Z',
      (e k : G') * z * (e k : G')⁻¹ = z) :
    CrossedHomPrincipal Q Z (K ⊔ H) Z' R' e := by
  classical
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨s⟩⟩ := exists_secRep hd.secHyp
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  haveI : Fact (leviRep le_sup_left s).IsIrreducible := ⟨hd.isIrreducible_leviRep hf s⟩
  obtain ⟨B, hB, hBnd⟩ := hd.exists_invariant_form hf s
  exact crossedHomPrincipal_of_secRep e hd.le_normalizer hd.conj_mem_center hR'Z' hZ'c hZ'2
    le_sup_left hd.conj_mem_levi hKZ' (secRepRestrict le_sup_left s) (leviRep le_sup_left s)
    (fun _ _ => rfl) (hd.exists_leviRep_ne_one hf s) B hB hBnd
    (hd.mem_B1_leviRep hf s)

end CFSG.Quasithin.F112R.St84

end
