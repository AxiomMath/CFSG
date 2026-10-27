module

public import CFSG.Quasithin.Recognition.St84.Weiss
public import CFSG.Quasithin.Recognition.St84.L2Facts

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
open scoped Pointwise MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem sylow_pretransitive_of_card_prime_pow {p k : ℕ} [Fact p.Prime]
    {H α : Type*} [Group H] [MulAction H α] [Finite H] [Finite α]
    (hcard : Nat.card α = p ^ k) (htrans : ∀ a b : α, ∃ h : H, h • a = b)
    {P : Subgroup H} (hP2 : IsPGroup p P) (hPidx : ¬ p ∣ P.index)
    (a b : α) : ∃ g ∈ P, g • a = b := by
  classical
  let H0 : Subgroup H := MulAction.stabilizer H b
  let q : ℕ := Nat.card (H0.subgroupOf P)
  let r : ℕ := (MulAction.stabilizer (↥P) b).index
  have hstab : MulAction.stabilizer (↥P) b = H0.subgroupOf P :=
    (MulAction.stabilizer_subgroupOf P b).symm
  have hq : q = Nat.card (MulAction.stabilizer (↥P) b) := by
    show Nat.card (H0.subgroupOf P) = _
    rw [hstab]
  have hr : r = (MulAction.orbit (↥P) b).ncard := by
    show (MulAction.stabilizer (↥P) b).index = _
    exact MulAction.index_stabilizer (↥P) b
  have hPcard : q * r = Nat.card P := by
    rw [hq]
    exact Subgroup.card_mul_index (MulAction.stabilizer (↥P) b)
  have horbH : MulAction.orbit H b = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact htrans b x
  have hidxH0 : H0.index = p ^ k := by
    show (MulAction.stabilizer H b).index = p ^ k
    rw [MulAction.index_stabilizer H b, horbH, Set.ncard_univ, hcard]
  have hH0card : Nat.card H0 * p ^ k = Nat.card H := by
    rw [← hidxH0]
    exact Subgroup.card_mul_index H0
  have hHcard : Nat.card H = Nat.card P * P.index :=
    (Subgroup.card_mul_index P).symm
  have hq_dvd : q ∣ Nat.card H0 := by
    let f : ↥(H0.subgroupOf P) →* ↥H0 :=
      { toFun := fun x => ⟨(x.1 : H), x.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    have hf : Function.Injective f := by
      intro x y hxy
      have h2 : (x.1 : H) = (y.1 : H) := congrArg (fun z : ↥H0 => (z : H)) hxy
      exact Subtype.ext (Subtype.ext h2)
    exact Subgroup.card_dvd_of_injective f hf
  obtain ⟨m, hm⟩ := hq_dvd
  have hqpos : 0 < q := by
    haveI : Nonempty (↥(H0.subgroupOf P)) := ⟨1⟩
    exact Nat.card_pos
  have hEq : m * p ^ k = r * P.index := by
    have h1 : q * (m * p ^ k) = Nat.card H := by
      rw [← mul_assoc, ← hm, hH0card]
    have h2 : q * (r * P.index) = Nat.card H := by
      rw [← mul_assoc, hPcard, hHcard]
    exact Nat.mul_left_cancel hqpos (h1.trans h2.symm)
  have hcop : Nat.Coprime (p ^ k) P.index :=
    ((Fact.out : p.Prime).coprime_pow_of_not_dvd hPidx).symm
  have hdvd : p ^ k ∣ r := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [← hEq]
    exact dvd_mul_left (p ^ k) m
  have hrle : r ≤ p ^ k := by
    rw [hr, ← hcard]
    simpa using Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit (↥P) b)) (Set.toFinite _)
  have hrpos : 0 < r := by
    rw [hr]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨b, MulAction.mem_orbit_self b⟩
  have hr_eq : r = p ^ k := Nat.le_antisymm hrle (Nat.le_of_dvd hrpos hdvd)
  have horb : MulAction.orbit (↥P) b = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, hcard, ← hr, hr_eq]
  have ha : a ∈ MulAction.orbit (↥P) b := by
    rw [horb]
    exact Set.mem_univ a
  obtain ⟨g, hg⟩ := ha
  refine ⟨g⁻¹, P.inv_mem g.2, ?_⟩
  rw [← hg]
  simp only [Subgroup.smul_def, ← mul_smul]
  simp

theorem sylow_pretransitive_of_card_prime_pow_sylow {p k : ℕ} [Fact p.Prime]
    {H α : Type*} [Group H] [MulAction H α] [Finite H] [Finite α]
    (hcard : Nat.card α = p ^ k) (htrans : ∀ a b : α, ∃ h : H, h • a = b)
    (P : Sylow p H) (a b : α) : ∃ g ∈ (P : Subgroup H), g • a = b :=
  sylow_pretransitive_of_card_prime_pow hcard htrans P.isPGroup' P.not_dvd_index a b

theorem G1Set_transitive_neighborSet_gen (h : Hyp30 Γ G)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    (hs : IsSingularity Γ G s) {t : ℕ} (ht2 : 2 ≤ t) (hts : t ≤ s - 1)
    (P : Arc Γ t) :
    ∀ a b : V, Γ.Adj (P.vert t) a → a ≠ P.vert (t - 1) →
      Γ.Adj (P.vert t) b → b ≠ P.vert (t - 1) →
      ∃ g ∈ G1Set (Γ := Γ) (G := G) (P.vert '' Set.Icc 1 (t - 1)), g • a = b := by
  classical
  have ht1 : 1 ≤ t := by omega
  have hts' : t < s := by omega
  let H : Subgroup G := arcStab (G := G) P
  haveI hHfin : Finite H := by
    haveI := h.finite_stab (P.vert 0)
    exact Finite.of_injective
      (Subgroup.inclusion (arcStab_le_stabilizer P (i := 0) (Nat.zero_le t)))
      (Subgroup.inclusion_injective _)
  let Ω : SubMulAction H V :=
    { carrier := {x | Γ.Adj (P.vert t) x ∧ x ≠ P.vert (t - 1)}
      smul_mem' := by
        rintro g x ⟨hx1, hx2⟩
        refine ⟨?_, ?_⟩
        · have hgt : (g : G) • P.vert t = P.vert t :=
            (mem_arcStab P).mp g.2 t le_rfl
          have hadj := (h.adj_smul (g : G) (P.vert t) x).2 hx1
          rwa [hgt] at hadj
        · intro hcontra
          apply hx2
          have hgp : (g : G) • P.vert (t - 1) = P.vert (t - 1) :=
            (mem_arcStab P).mp g.2 (t - 1) (by omega)
          have hcontra' : (g : G) • x = P.vert (t - 1) := hcontra
          have : (g : G) • x = (g : G) • P.vert (t - 1) := by rw [hcontra', hgp]
          exact MulAction.injective (g : G) this }
  have hΩcard : Nat.card Ω = 2 ^ nOf Γ (P.vert t) := by
    have hset : (Ω : Set V) = Γ.neighborSet (P.vert t) \ {P.vert (t - 1)} := rfl
    change Nat.card ↥(Ω : Set V) = 2 ^ nOf Γ (P.vert t)
    rw [Nat.card_coe_set_eq, hset]
    have hcardΔ : (Γ.neighborSet (P.vert t)).ncard = 2 ^ nOf Γ (P.vert t) + 1 := by
      rw [← Nat.card_coe_set_eq, (h.valency (P.vert t)).2]
    have hmem : P.vert (t - 1) ∈ Γ.neighborSet (P.vert t) := by
      have hadj := (P.adj (t - 1) (by omega)).symm
      rwa [show t - 1 + 1 = t by omega] at hadj
    have h := Set.ncard_sdiff_singleton_add_one (s := Γ.neighborSet (P.vert t)) hmem
      (h.finite_neighborSet (P.vert t))
    omega
  haveI hΩfin : Finite Ω :=
    ((h.finite_neighborSet (P.vert t)).subset (fun x hx => hx.1)).to_subtype
  have hreg : Regular Γ G P := hs.2.1 t ht1 hts' P
  have htrans : ∀ x y : Ω, ∃ g : H, g • x = y := by
    intro x y
    obtain ⟨g, hg, hgxy⟩ := hreg.2 x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2
    exact ⟨⟨g, hg⟩, Subtype.ext (by
      show ((⟨g, hg⟩ : H) : G) • x.1 = y.1
      simpa using hgxy)⟩
  let S : Sylow 2 H := Classical.choice Sylow.nonempty
  have hStrans : ∀ x y : Ω, ∃ g ∈ (S : Subgroup H), g • x = y :=
    sylow_pretransitive_of_card_prime_pow_sylow hΩcard htrans S
  let S' : Subgroup G := (S : Subgroup H).map H.subtype
  have hS'2 : IsPGroup 2 S' := by
    change IsPGroup 2 ((S : Subgroup H).map H.subtype)
    exact S.isPGroup'.map H.subtype
  have hS'mem : ∀ g : G, g ∈ S' ↔ ∃ h ∈ (S : Subgroup H), (h : G) = g := by
    intro g
    change g ∈ (S : Subgroup H).map H.subtype ↔ _
    exact Subgroup.mem_map
  have hS'le : ∀ i, 1 ≤ i → i ≤ t - 1 → S' ≤ G1 (Γ := Γ) (G := G) (P.vert i) := by
    intro i hi1 hit
    refine hQ (P.vert i) S' hS'2 ?_ (P.vert (i - 1)) (P.vert (i + 1)) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      obtain ⟨h0, hh0, rfl⟩ := (hS'mem g).mp hg
      exact arcStab_le_stabilizer P (i := i) (by omega) (h0 : H).2
    · have hadj : Γ.Adj (P.vert i) (P.vert (i - 1)) := by
        have h := (P.adj (i - 1) (by omega)).symm
        rwa [show i - 1 + 1 = i by omega] at h
      exact hadj
    · exact P.adj i (by omega)
    · have hnb := P.nb (i - 1) (by omega)
      rwa [show i - 1 + 2 = i + 1 by omega] at hnb
    · intro g hg
      obtain ⟨h0, hh0, rfl⟩ := (hS'mem g).mp hg
      exact (mem_arcStab P).mp (h0 : H).2 (i - 1) (by omega)
    · intro g hg
      obtain ⟨h0, hh0, rfl⟩ := (hS'mem g).mp hg
      exact (mem_arcStab P).mp (h0 : H).2 (i + 1) (by omega)
  intro a b ha hab hb hbb
  obtain ⟨g, hgS, hg⟩ :=
    hStrans ⟨a, ⟨ha, hab⟩⟩ ⟨b, ⟨hb, hbb⟩⟩
  refine ⟨(g : G), ?_, ?_⟩
  · rw [mem_G1Set]
    rintro x ⟨i, ⟨hi1, hit⟩, rfl⟩
    exact hS'le i hi1 hit ((hS'mem (g : G)).mpr ⟨g, hgS, rfl⟩)
  · have hval : (g : H) • a = b := congrArg Subtype.val hg
    show ((g : H) : G) • a = b
    rw [← Subgroup.smul_def]
    exact hval

theorem G1Set_transitive_neighborSet (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    (hs : IsSingularity Γ G s) {t : ℕ} (ht2 : 2 ≤ t) (hts : t ≤ s - 1)
    (P : Arc Γ t) :
    ∀ a b : V, Γ.Adj (P.vert t) a → a ≠ P.vert (t - 1) →
      Γ.Adj (P.vert t) b → b ≠ P.vert (t - 1) →
      ∃ g ∈ G1Set (Γ := Γ) (G := G) (P.vert '' Set.Icc 1 (t - 1)), g • a = b :=
  G1Set_transitive_neighborSet_gen h hQ hs ht2 hts P

theorem pCoreOf_edge_ne_bot (h : Hyp30 Γ G) {x y : V} (hxy : Γ.Adj x y) :
    pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) ≠ ⊥ := by
  classical
  obtain ⟨N, hN⟩ := h.locL2 x
  have hn1 : 1 ≤ nOf Γ x := (h.valency x).1
  have hcard : Nat.card (Γ.neighborSet x) = 2 ^ nOf Γ x + 1 := (h.valency x).2
  have hfin : Finite (MulAction.stabilizer G x) := h.finite_stab x
  have hNle : N ≤ MulAction.stabilizer G x := hN.le
  have hNnorm : MulAction.stabilizer G x ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN.le).mp hN.normal
  let U : Sylow 2 N := hN.pointSylowN h.adj_smul hfin hcard hn1 y
  let BN : Subgroup N := hN.pointSubgroup y
  let B : Subgroup G := N ⊓ MulAction.stabilizer G y
  let C : Subgroup G := MulAction.stabilizer G x ⊓ MulAction.stabilizer G y
  have hUne : (U : Subgroup N) ≠ ⊥ := by
    let P₀ : Subgroup (PSL(2, GaloisField 2 (nOf Γ x))) :=
      hN.pointSylow h.adj_smul hfin hcard hn1 y
    have hP0ne : P₀ ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, psl2_sylow_two_card hn1]
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ nOf Γ x := Nat.pow_le_pow_right (by norm_num) hn1
    obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP0ne
    obtain ⟨w, hw⟩ := hN.phi_surjective (z : PSL(2, GaloisField 2 (nOf Γ x)))
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨w, ?_⟩, ?_⟩
    · have hUeq : (U : Subgroup N) = Subgroup.comap hN.phi P₀ := rfl
      rw [hUeq, Subgroup.mem_comap, hw]
      exact z.2
    · intro hw1
      apply hzne
      have hw_eq : w = 1 := congrArg Subtype.val hw1
      have h1 : hN.phi w = 1 := by rw [hw_eq, map_one]
      rw [hw] at h1
      exact Subtype.ext h1
  let X : Subgroup G := (U : Subgroup N).map N.subtype
  have hX2 : IsPGroup 2 X := U.isPGroup'.map N.subtype
  have hXne : X ≠ ⊥ := by
    obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨(z : N), Subgroup.mem_map_of_mem N.subtype z.2⟩, fun hz1 => hzne ?_⟩
    have h1 : ((z : N) : G) = 1 := congrArg Subtype.val hz1
    exact Subtype.ext (N.subtype_injective h1)
  have hBNeq : BN.map N.subtype = B := by
    show ((N ⊓ MulAction.stabilizer G y).subgroupOf N).map N.subtype = B
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have hBNnorm : BN = Subgroup.normalizer (U : Subgroup N) :=
    hN.pointSubgroup_eq_normalizer_pointSylowN h.adj_smul hfin hcard hn1 hxy
  have hUleBN : (U : Subgroup N) ≤ BN := by
    rw [hBNnorm]
    exact Subgroup.le_normalizer
  have hXB : X ≤ B := by
    rw [← hBNeq]
    exact Subgroup.map_mono hUleBN
  have hBnormX : B ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hBNeq, hBNnorm]
    exact Subgroup.le_normalizer_map N.subtype
  have hXpB : X ≤ pCoreOf 2 B :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXB hBnormX hX2
  have hBC : B ≤ C := by
    intro g hg
    exact Subgroup.mem_inf.mpr
      ⟨hNle (Subgroup.mem_inf.mp hg).1, (Subgroup.mem_inf.mp hg).2⟩
  have hCnormB : C ≤ Subgroup.normalizer (B : Set G) := by
    intro c hc
    obtain ⟨hcx, hcy⟩ := Subgroup.mem_inf.mp hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub c B = B
    rw [show B = N ⊓ MulAction.stabilizer G y from rfl, conjSub_inf]
    have h1 : conjSub c N = N := by
      have hcN : c ∈ Subgroup.normalizer (N : Set G) := hNnorm hcx
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at hcN
    have h2 : conjSub c (MulAction.stabilizer G y) = MulAction.stabilizer G y := by
      rw [← stabilizer_smul_eq_conjSub, MulAction.mem_stabilizer_iff.mp hcy]
    rw [h1, h2]
  have hpCore : pCoreOf 2 B ≤ pCoreOf 2 C :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 B).trans hBC)
      (hCnormB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B))
      ((CFSG.pCore_isPGroup (p := 2) (G := B)).map B.subtype)
  intro hbot
  apply hXne
  rw [eq_bot_iff]
  intro g hg
  have hgm : g ∈ pCoreOf 2 C := hpCore (hXpB hg)
  rwa [hbot] at hgm

theorem centerOf_pCoreOf_edge_ne_bot (h : Hyp30 Γ G) {x y : V} (hxy : Γ.Adj x y) :
    centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)) ≠ ⊥ := by
  classical
  let S : Subgroup G := pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)
  have hSne : S ≠ ⊥ := pCoreOf_edge_ne_bot h hxy
  have hSp : IsPGroup 2 S := by
    let H0 : Subgroup G := MulAction.stabilizer G x ⊓ MulAction.stabilizer G y
    have h : IsPGroup 2 (CFSG.pCore 2 H0) := CFSG.pCore_isPGroup (p := 2) (G := H0)
    exact h.map H0.subtype
  have hSle : S ≤ MulAction.stabilizer G x :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2
      (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)).trans inf_le_left
  haveI : Finite ↥S := by
    haveI := h.finite_stab x
    exact Finite.of_injective (Subgroup.inclusion hSle) (Subgroup.inclusion_injective _)
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  have hcenter : Subgroup.center ↥S ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hSp.center_nontrivial
  intro hbot
  have hsub : (centerOf S).subgroupOf S = Subgroup.center ↥S := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
    constructor
    · intro hz y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2) y y.2)
    · intro hz
      exact Subgroup.mem_inf.mpr
        ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
          congrArg Subtype.val (hz ⟨y, hy⟩)⟩
  rw [hbot, Subgroup.bot_subgroupOf] at hsub
  exact hcenter hsub.symm

theorem G1_inf_G1_le_pCoreOf_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {x y w : V} (hxy : Γ.Adj x y) (hyw : Γ.Adj y w) (hxw : w ≠ x) :
    G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w ≤
      pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) := by
  classical
  let X : Subgroup G := G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w
  let A : Subgroup G := G1 (Γ := Γ) (G := G) y
  let B : Subgroup G := MulAction.stabilizer G x ⊓ MulAction.stabilizer G y
  haveI : Finite A := finite_G1 h y
  have hX2 : IsPGroup 2 X := G1_pair_isPGroup_gen h hs hev hs6 T hK hyw
  have hXA : X ≤ A := inf_le_left
  have hAn : A ≤ Subgroup.normalizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub a X = X
    rw [show X = G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w from rfl, conjSub_inf]
    have h1 : conjSub a (G1 (Γ := Γ) (G := G) y) = G1 (Γ := Γ) (G := G) y := by
      rw [conjSub_G1 h, MulAction.mem_stabilizer_iff.mp (G1_le_stabilizer y ha)]
    have h2 : conjSub a (G1 (Γ := Γ) (G := G) w) = G1 (Γ := Γ) (G := G) w := by
      rw [conjSub_G1 h, G1_fixes_adj hyw a ha]
    rw [h1, h2]
  have hAB : A ≤ B := by
    intro a ha
    exact Subgroup.mem_inf.mpr
      ⟨G1_fixes_adj hxy.symm a ha, MulAction.mem_stabilizer_iff.mpr (G1_fixes y a ha)⟩
  have hBn : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    exact stabilizer_le_normalizer_G1 h y (Subgroup.mem_inf.mp hb).2
  exact le_pCoreOf_of_two_normal hX2 hXA hAn hAB hBn

theorem G1_inf_G1_le_pCoreOf (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {x y w : V} (hxy : Γ.Adj x y) (hyw : Γ.Adj y w) (hxw : w ≠ x) :
    G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w ≤
      pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) :=
  G1_inf_G1_le_pCoreOf_gen h hs hev hs6 T hK hxy hyw hxw

theorem G1Set_pair (a b : V) :
    G1Set (Γ := Γ) (G := G) ({a, b} : Set V) =
      G1 (Γ := Γ) (G := G) a ⊓ G1 (Γ := Γ) (G := G) b := by
  apply le_antisymm
  · intro g hg
    exact Subgroup.mem_inf.mpr
      ⟨(mem_G1Set.mp hg) a (Set.mem_insert a {b}),
       (mem_G1Set.mp hg) b (Set.mem_insert_of_mem a rfl)⟩
  · intro g hg
    rw [mem_G1Set]
    intro x hx
    rcases hx with rfl | rfl
    · exact (Subgroup.mem_inf.mp hg).1
    · exact (Subgroup.mem_inf.mp hg).2

theorem centerOf_pCoreOf_edge_fixes_neighbors_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y w : V} (hxy : Γ.Adj x y) (hyw : Γ.Adj y w) (hxw : w ≠ x)
    {b : G} (hb : b ∈ centerOf (pCoreOf 2
      (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y))) :
    b • w = w := by
  classical
  by_contra hbw
  have hbS : b ∈ pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) :=
    (Subgroup.mem_inf.mp hb).1
  have hbxy : b ∈ MulAction.stabilizer G x ⊓ MulAction.stabilizer G y :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hbS
  have hby : b • y = y :=
    MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hbxy).2
  have hXle : G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w ≤
      pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) :=
    G1_inf_G1_le_pCoreOf_gen h hs hev hs6 T hK hxy hyw hxw
  have hcomm : ∀ g ∈ G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w, g * b = b * g :=
    fun g hg => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2) g (hXle hg)
  have hconj : conjSub b (G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w) =
      G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w := by
    ext z
    rw [mem_conjSub]
    constructor
    · intro hz
      have h := hcomm (b⁻¹ * z * b) hz
      have hz' : z = b⁻¹ * z * b := by
        calc z = b * (b⁻¹ * z * b) * b⁻¹ := by group
          _ = ((b⁻¹ * z * b) * b) * b⁻¹ := by rw [← h]
          _ = b⁻¹ * z * b := by group
      rw [hz']
      exact hz
    · intro hz
      have h := hcomm z hz
      have hz' : b⁻¹ * z * b = z := by
        calc b⁻¹ * z * b = b⁻¹ * (z * b) := by group
          _ = b⁻¹ * (b * z) := by rw [h]
          _ = z := by group
      rw [hz']
      exact hz
  have hXeq : G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w =
      G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) (b • w) := by
    rw [← hconj, conjSub_inf, conjSub_G1 h, conjSub_G1 h, hby]
  have hXfix : G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w ≤
      G1 (Γ := Γ) (G := G) (b • w) := by
    rw [hXeq]
    exact inf_le_right
  have hwbw : w ≠ b • w := fun h => hbw h.symm
  have hybw : Γ.Adj y (b • w) := by
    have h' := (h.adj_smul b y w).2 hyw
    rwa [hby] at h'
  have hdeg : 3 ≤ Nat.card (Γ.neighborSet w) :=
    h.three_le_card w
  obtain ⟨z, hzw, hzy, hzbw⟩ :=
    exists_adj_ne_ne (Γ := Γ) (v := w) (a := y) (b := b • w) hdeg
  let Q : Arc Γ 3 := Arc.three hzw.symm hyw.symm hybw hzy hwbw
  have hQ1 : Q.vert 1 = w := by simp [Q, Arc.three]
  have hQ2 : Q.vert 2 = y := by simp [Q, Arc.three]
  have hQ3 : Q.vert 3 = b • w := by simp [Q, Arc.three]
  have hQset : Q.vert '' Set.Icc 1 2 ⊆ ({w, y} : Set V) := by
    rintro v ⟨i, hi, rfl⟩
    have hi' : i = 1 ∨ i = 2 := by
      simp only [Set.mem_Icc] at hi
      omega
    rcases hi' with rfl | rfl
    · rw [hQ1]; exact Set.mem_insert _ _
    · rw [hQ2]; exact Set.mem_insert_of_mem _ rfl
  have htrans := G1Set_transitive_neighborSet_gen h hQ hs (t := 3) (by norm_num) (by omega) Q
  obtain ⟨z1, hz1adj, hz1y⟩ := h.exists_adj_ne (b • w) y
  have hdeg' : 3 ≤ Nat.card (Γ.neighborSet (b • w)) :=
    h.three_le_card (b • w)
  obtain ⟨z2, hz2adj, hz2y, hz2z1⟩ :=
    exists_adj_ne_ne (Γ := Γ) (v := b • w) (a := y) (b := z1) hdeg'
  obtain ⟨g, hgmem, hg⟩ := htrans z1 z2 hz1adj hz1y hz2adj hz2y
  have hgX : g ∈ G1 (Γ := Γ) (G := G) y ⊓ G1 (Γ := Γ) (G := G) w := by
    have h1 := (mem_G1Set.mp hgmem) w ⟨1, by norm_num, hQ1⟩
    have h2 := (mem_G1Set.mp hgmem) y ⟨2, by norm_num, hQ2⟩
    exact Subgroup.mem_inf.mpr ⟨h2, h1⟩
  have hgz2 : g • z2 = z2 := G1_fixes_adj hz2adj g (hXfix hgX)
  have hEq : g • z1 = g • z2 := by rw [hg, hgz2]
  exact hz2z1 (MulAction.injective g hEq).symm

theorem centerOf_pCoreOf_edge_fixes_neighbors (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y w : V} (hxy : Γ.Adj x y) (hyw : Γ.Adj y w) (hxw : w ≠ x)
    {b : G} (hb : b ∈ centerOf (pCoreOf 2
      (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y))) :
    b • w = w :=
  centerOf_pCoreOf_edge_fixes_neighbors_gen h hs hev hs6 T hK hQ hxy hyw hxw hb

theorem centerOf_pCoreOf_edge_fixes_arc_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y : V} (hxy : Γ.Adj x y)
    {b : G} (hb : b ∈ centerOf (pCoreOf 2
      (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)))
    (Q : Arc Γ (s - 1)) (hQ0 : Q.vert 0 = x) (hQ1 : Q.vert 1 = y) :
    ∀ i, i ≤ s / 2 → b • Q.vert i = Q.vert i := by
  classical
  have hbS : b ∈ pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) :=
    (Subgroup.mem_inf.mp hb).1
  have hbxy : b ∈ MulAction.stabilizer G x ⊓ MulAction.stabilizer G y :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hbS
  have hbx : b • x = x := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hbxy).1
  have hby : b • y = y := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hbxy).2
  have hb0 : b • Q.vert 0 = Q.vert 0 := by rw [hQ0]; exact hbx
  have hb1 : b • Q.vert 1 = Q.vert 1 := by rw [hQ1]; exact hby
  have hs1 : 2 ≤ s - 1 := by omega
  have hQ2adj : Γ.Adj y (Q.vert 2) := by
    have h' := Q.adj 1 (by omega)
    rwa [hQ1] at h'
  have hQ2ne : Q.vert 2 ≠ x := by
    intro h
    exact (Q.nb 0 (by omega)) (by rw [hQ0, h])
  have hb2 : b • Q.vert 2 = Q.vert 2 :=
    centerOf_pCoreOf_edge_fixes_neighbors_gen h hs hev hs6 T hK hQ hxy hQ2adj hQ2ne hb
  have key : ∀ n, 2 ≤ n → n + 1 ≤ s - 1 → (∀ j ≤ n, b • Q.vert j = Q.vert j) →
      b • Q.vert (n + 1) = Q.vert (n + 1) ∨ s - 1 ≤ 2 * n := by
    intro n hn2 hnlt hfix
    by_cases hfixn : b • Q.vert (n + 1) = Q.vert (n + 1)
    · exact Or.inl hfixn
    · refine Or.inr ?_
      by_contra hbig
      have hle : n + 1 ≤ s - 2 := by omega
      have htrans := G1Set_transitive_neighborSet_gen h hQ hs (t := s - 1) (by omega) le_rfl Q
      obtain ⟨p1, hp1adj, hp1ne⟩ := h.exists_adj_ne (Q.vert (s - 1)) (Q.vert (s - 2))
      have hdeg : 3 ≤ Nat.card (Γ.neighborSet (Q.vert (s - 1))) :=
        h.three_le_card (Q.vert (s - 1))
      obtain ⟨p2, hp2adj, hp2ne, hp2p1⟩ :=
        exists_adj_ne_ne (Γ := Γ) (v := Q.vert (s - 1)) (a := Q.vert (s - 2)) (b := p1) hdeg
      obtain ⟨a, hamem, haap⟩ := htrans p1 p2 hp1adj hp1ne hp2adj hp2ne
      have ha1 : a ≠ 1 := by
        intro h1
        rw [h1, one_smul] at haap
        exact hp2p1 haap.symm
      have haQ : ∀ j, 1 ≤ j → j ≤ s - 2 → a ∈ G1 (Γ := Γ) (G := G) (Q.vert j) :=
        fun j hj1 hj2 => (mem_G1Set.mp hamem) (Q.vert j) ⟨j, ⟨hj1, hj2⟩, rfl⟩
      have haS : a ∈ pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) :=
        G1_inf_G1_le_pCoreOf_gen h hs hev hs6 T hK hxy hQ2adj hQ2ne
          (Subgroup.mem_inf.mpr ⟨by rw [← hQ1]; exact haQ 1 (by norm_num) (by omega),
            haQ 2 (by norm_num) (by omega)⟩)
      have hab : a * b = b * a :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2) a haS
      have haQb : ∀ j, n + 1 ≤ j → j ≤ s - 2 → a ∈ G1 (Γ := Γ) (G := G) (b⁻¹ • Q.vert j) := by
        intro j hj1 hj2
        have hmem : b⁻¹ * a * b ∈ conjSub b⁻¹ (G1 (Γ := Γ) (G := G) (Q.vert j)) := by
          simpa using mul_mem_conjSub (g := b⁻¹) (haQ j (by omega) hj2)
        have hcomm : b⁻¹ * a * b = a := by
          calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
            _ = b⁻¹ * (b * a) := by rw [hab]
            _ = a := by group
        rw [hcomm, conjSub_G1 h] at hmem
        exact hmem
      let k : ℕ := s - 2 - n
      have hk2 : 2 ≤ k := by omega
      have hk_le : k ≤ s - 2 := by omega
      have hkn : s - 2 - k = n := by omega
      let Q' : Arc Γ (s - 2) := initialArc Q (s - 2) (by omega)
      have hQ' : ∀ i, Q'.vert i = Q.vert i := fun i => initialArc_vert Q (s - 2) (by omega) i
      let T1 : Arc Γ k := suffixArc Q' k hk_le
      have hT1 : ∀ i, T1.vert i = Q.vert (n + i) := by
        intro i
        rw [show T1.vert i = Q'.vert (i + ((s - 2) - k)) from rfl, hQ']
        congr 1
        omega
      let A : Arc Γ k := T1.rev
      have hA : ∀ i, i ≤ k → A.vert i = Q.vert (s - 2 - i) := by
        intro i hi
        rw [show A.vert i = T1.vert (k - i) from Arc.rev_vert T1 i, hT1]
        congr 1
        omega
      let T2 : Arc Γ (k - 1) := suffixArc Q' (k - 1) (by omega)
      have hT2 : ∀ i, T2.vert i = Q.vert (n + 1 + i) := by
        intro i
        rw [show T2.vert i = Q'.vert (i + ((s - 2) - (k - 1))) from rfl, hQ']
        congr 1
        omega
      let B : Arc Γ (k - 1) := smulArc h.adj_smul b⁻¹ T2
      have hB : ∀ i, B.vert i = b⁻¹ • Q.vert (n + 1 + i) := by
        intro i
        rw [show B.vert i = b⁻¹ • T2.vert i from rfl, hT2]
      have hEadj : Γ.Adj (Q.vert n) (b⁻¹ • Q.vert (n + 1)) := by
        have hbn : b⁻¹ • Q.vert n = Q.vert n := by
          calc b⁻¹ • Q.vert n = b⁻¹ • (b • Q.vert n) := by rw [hfix n le_rfl]
            _ = Q.vert n := by rw [inv_smul_smul]
        have h' := (h.adj_smul b⁻¹ (Q.vert n) (Q.vert (n + 1))).2 (Q.adj n (by omega))
        rwa [hbn] at h'
      let E : Arc Γ 1 := Arc.step (Q.vert n) (b⁻¹ • Q.vert (n + 1)) hEadj
      have hE0 : E.vert 0 = Q.vert n := by simp [E, Arc.step]
      have hE1 : E.vert 1 = b⁻¹ • Q.vert (n + 1) := by simp [E, Arc.step]
      have h1 : A.vert k = E.vert 0 := by rw [hA k le_rfl, hE0, hkn]
      have hnb1 : 1 ≤ k → 1 ≤ 1 → A.vert (k - 1) ≠ E.vert 1 := by
        intro _ _
        rw [hA (k - 1) (by omega), hE1, show s - 2 - (k - 1) = n + 1 by omega]
        intro hcontra
        apply hfixn
        have h' : b • Q.vert (n + 1) = Q.vert (n + 1) := by
          have h1' := congrArg (fun z => b • z) hcontra
          simpa using h1'
        exact h'
      let R1 : Arc Γ (k + 1) := Arc.append A E h1 hnb1
      have hR1 : ∀ i, i ≤ k → R1.vert i = Q.vert (s - 2 - i) := by
        intro i hi
        rw [show R1.vert i = A.vert i from Arc.append_vert_le A E h1 hnb1 hi]
        exact hA i hi
      have hR1k : R1.vert k = Q.vert n := by rw [hR1 k le_rfl, hkn]
      have hR1k1 : R1.vert (k + 1) = b⁻¹ • Q.vert (n + 1) :=
        (Arc.append_vert_ge A E h1 hnb1 (by omega : k ≤ k + 1)).trans
          (by rw [show k + 1 - k = 1 by omega, hE1])
      have h2 : R1.vert (k + 1) = B.vert 0 := by rw [hR1k1, hB]
      have hnb2 : 1 ≤ k + 1 → 1 ≤ k - 1 → R1.vert (k + 1 - 1) ≠ B.vert 1 := by
        intro _ _
        rw [show k + 1 - 1 = k by omega, hR1k, hB]
        rw [show n + 1 + 1 = n + 2 by omega]
        intro hcontra
        have h' : Q.vert n = Q.vert (n + 2) := by
          have h1' := congrArg (fun z => b • z) hcontra
          simpa [hfix n le_rfl] using h1'
        exact (Q.nb n (by omega)) h'
      let R : Arc Γ (2 * k) := arcCast (by omega : (k + 1) + (k - 1) = 2 * k)
        (Arc.append R1 B h2 hnb2)
      have hR : ∀ i, i ≤ 2 * k → a ∈ G1 (Γ := Γ) (G := G) (R.vert i) := by
        intro i hi
        rw [show R.vert i = (Arc.append R1 B h2 hnb2).vert i from arcCast_vert _ _ i]
        by_cases hik : i ≤ k
        · rw [show (Arc.append R1 B h2 hnb2).vert i = R1.vert i from
            Arc.append_vert_le R1 B h2 hnb2 (by omega : i ≤ k + 1)]
          rw [hR1 i hik]
          exact haQ (s - 2 - i) (by omega) (by omega)
        · have hik' : k + 1 ≤ i := by omega
          rw [Arc.append_vert_ge R1 B h2 hnb2 hik', hB]
          exact haQb (n + 1 + (i - (k + 1))) (by omega) (by omega)
      have hRbot : G1Set (Γ := Γ) (G := G) (R.vert '' Set.Icc 0 (2 * k)) = ⊥ :=
        G1Set_arc_eq_bot_gen h hs hev hs6 T hK (m := 2 * k) (by omega) R
      have hamem' : a ∈ G1Set (Γ := Γ) (G := G) (R.vert '' Set.Icc 0 (2 * k)) := by
        rw [mem_G1Set]
        rintro v ⟨i, hi, rfl⟩
        exact hR i (by simpa using hi)
      rw [hRbot] at hamem'
      exact ha1 (by simpa using hamem')
  intro i hi
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi2 : i ≤ 2
    · interval_cases i
      · exact hb0
      · exact hb1
      · exact hb2
    · have hi3 : 3 ≤ i := by omega
      have hprefix : ∀ j ≤ i - 1, b • Q.vert j = Q.vert j := by
        intro j hj
        exact ih j (by omega) (by omega)
      rcases key (i - 1) (by omega) (by omega) hprefix with h' | h'
      · simpa [show i - 1 + 1 = i by omega] using h'
      · have h2i : 2 * i ≤ s := by
          calc 2 * i = i * 2 := by ring
            _ ≤ (s / 2) * 2 := Nat.mul_le_mul_right 2 hi
            _ ≤ s := Nat.div_mul_le_self s 2
        omega

theorem centerOf_pCoreOf_edge_fixes_arc (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y : V} (hxy : Γ.Adj x y)
    {b : G} (hb : b ∈ centerOf (pCoreOf 2
      (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)))
    (Q : Arc Γ (s - 1)) (hQ0 : Q.vert 0 = x) (hQ1 : Q.vert 1 = y) :
    ∀ i, i ≤ s / 2 → b • Q.vert i = Q.vert i :=
  centerOf_pCoreOf_edge_fixes_arc_gen h hs hev hs6 T hK hQ hxy hb Q hQ0 hQ1

theorem exists_arc_extend (hdeg : ∀ u v : V, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v)
    (hex : ∀ u : V, ∃ w, Γ.Adj u w) {m : ℕ} (P : Arc Γ m) :
    ∀ k : ℕ, m ≤ k → ∃ Q : Arc Γ k, ∀ i, i ≤ m → Q.vert i = P.vert i := by
  intro k hk
  have main : ∀ d : ℕ, ∃ Q : Arc Γ (m + d), ∀ i, i ≤ m → Q.vert i = P.vert i := by
    intro d
    induction d with
    | zero => exact ⟨P, fun i _ => rfl⟩
    | succ d ih =>
      obtain ⟨Q, hQ⟩ := ih
      by_cases h0 : m + d = 0
      · obtain ⟨w, hw⟩ := hex (Q.vert 0)
        refine ⟨arcCast (by omega : 1 = m + (d + 1)) (Arc.step (Q.vert 0) w hw), ?_⟩
        intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        rw [arcCast_vert]
        simpa [Arc.step] using hQ 0 (by omega)
      · obtain ⟨w, hw, hwne⟩ := hdeg (Q.vert (m + d)) (Q.vert (m + d - 1)) (by
          have h := (Q.adj (m + d - 1) (by omega)).symm
          rwa [show m + d - 1 + 1 = m + d by omega] at h)
        refine ⟨arcCast (by omega : (m + d) + 1 = m + (d + 1))
          (snocArc Q w hw (fun _ => hwne)), ?_⟩
        intro i hi
        rw [arcCast_vert, snocArc_vert_le Q w hw (fun _ => hwne) (by omega)]
        exact hQ i hi
  obtain ⟨d, rfl⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
  exact main d

theorem exists_arc_through (h : Hyp30 Γ G) {x y v : V} (hxy : Γ.Adj x y)
    (hd : Γ.dist x v = Γ.dist y v + 1) (hle : Γ.dist x v ≤ s - 2) :
    ∃ Q : Arc Γ (s - 1), Q.vert 0 = x ∧ Q.vert 1 = y ∧ Q.vert (Γ.dist x v) = v := by
  classical
  have hdeg : ∀ u w : V, Γ.Adj u w → ∃ z, Γ.Adj u z ∧ z ≠ w := fun u w _ => h.exists_adj_ne u w
  have hex : ∀ u : V, ∃ z, Γ.Adj u z := h.exists_adj
  obtain ⟨A, hA0, hAd⟩ := IsTree.exists_arc_between h.isTree y v
  have hxsym : Γ.Adj x (A.vert 0) := by rw [hA0]; exact hxy
  have hx' : 1 ≤ Γ.dist y v → x ≠ A.vert 1 := by
    intro hd1 heq
    have htri := h.isTree.connected.dist_triangle (u := x) (v := A.vert 1) (w := v)
    have h1 : Γ.dist (A.vert 1) v = Γ.dist y v - 1 := by
      have h2 := Arc.dist_vert h.isTree A (i := 1) (j := Γ.dist y v) hd1 le_rfl
      rwa [hAd] at h2
    have h0 : Γ.dist x (A.vert 1) = 0 := by rw [heq, SimpleGraph.dist_self]
    rw [h0, zero_add] at htri
    omega
  let P : Arc Γ (Γ.dist y v + 1) := consArc A x hxsym hx'
  have hP0 : P.vert 0 = x := consArc_vert_zero A x hxsym hx'
  have hP1 : P.vert 1 = y := by rw [consArc_vert_succ, hA0]
  have hPd : P.vert (Γ.dist x v) = v := by
    rw [hd, consArc_vert_succ, hAd]
  have hPle : Γ.dist y v + 1 ≤ s - 1 := by rw [← hd]; omega
  obtain ⟨Q, hQ⟩ := exists_arc_extend hdeg hex P (s - 1) hPle
  exact ⟨Q, by rw [hQ 0 (by omega), hP0], by rw [hQ 1 (by omega), hP1],
    by rw [hQ (Γ.dist x v) (by omega), hPd]⟩

theorem centerOf_pCoreOf_edge_le_GmPair_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y : V} (hxy : Γ.Adj x y) :
    centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)) ≤
      GmPair (Γ := Γ) (G := G) (s / 2 - 1) x y := by
  classical
  intro b hb
  have hbS : b ∈ pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) :=
    (Subgroup.mem_inf.mp hb).1
  have hbxy : b ∈ MulAction.stabilizer G x ⊓ MulAction.stabilizer G y :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hbS
  have hbx : b • x = x := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hbxy).1
  have hby : b • y = y := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hbxy).2
  have hsm : s / 2 ≤ s - 2 := by omega
  have hfix_fwd : ∀ v : V, Γ.dist x v = Γ.dist y v + 1 → Γ.dist x v ≤ s / 2 → b • v = v := by
    intro v hd hdle
    obtain ⟨Q, hQ0, hQ1, hQv⟩ := exists_arc_through h hxy hd (le_trans hdle hsm)
    have h := centerOf_pCoreOf_edge_fixes_arc_gen h hs hev hs6 T hK hQ hxy hb Q hQ0 hQ1
      (Γ.dist x v) hdle
    rwa [hQv] at h
  have hfix_bwd : ∀ v : V, Γ.dist y v = Γ.dist x v + 1 → Γ.dist y v ≤ s / 2 → b • v = v := by
    intro v hd hdle
    obtain ⟨Q, hQ0, hQ1, hQv⟩ := exists_arc_through h hxy.symm hd (le_trans hdle hsm)
    have hb' : b ∈ centerOf (pCoreOf 2
        (MulAction.stabilizer G y ⊓ MulAction.stabilizer G x)) := by
      rwa [inf_comm]
    have h := centerOf_pCoreOf_edge_fixes_arc_gen h hs hev hs6 T hK hQ hxy.symm hb' Q hQ0 hQ1
      (Γ.dist y v) hdle
    rwa [hQv] at h
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_Gm]
    intro v hv
    rcases IsTree.dist_adj_cases h.isTree hxy (r := v) with hcase | hcase
    · rw [SimpleGraph.dist_comm (u := v) (v := y),
        SimpleGraph.dist_comm (u := v) (v := x)] at hcase
      exact hfix_bwd v hcase (by omega)
    · rw [SimpleGraph.dist_comm (u := v) (v := x),
        SimpleGraph.dist_comm (u := v) (v := y)] at hcase
      exact hfix_fwd v hcase (by omega)
  · rw [mem_Gm]
    intro v hv
    rcases IsTree.dist_adj_cases h.isTree hxy (r := v) with hcase | hcase
    · rw [SimpleGraph.dist_comm (u := v) (v := y),
        SimpleGraph.dist_comm (u := v) (v := x)] at hcase
      exact hfix_bwd v hcase (by omega)
    · rw [SimpleGraph.dist_comm (u := v) (v := x),
        SimpleGraph.dist_comm (u := v) (v := y)] at hcase
      exact hfix_fwd v hcase (by omega)

theorem centerOf_pCoreOf_edge_le_GmPair (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y : V} (hxy : Γ.Adj x y) :
    centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)) ≤
      GmPair (Γ := Γ) (G := G) (s / 2 - 1) x y :=
  centerOf_pCoreOf_edge_le_GmPair_gen h hs hev hs6 T hK hQ hxy

theorem conjSub_Gm (h : Hyp30 Γ G) (g : G) (k : ℕ) (v : V) :
    conjSub g (Gm (Γ := Γ) (G := G) k v) = Gm (Γ := Γ) (G := G) k (g • v) := by
  rw [Gm, Gm, conjSub_fixSet]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    show Γ.dist (g • v) (g • z) ≤ k
    rw [IsTree.dist_smul h.isTree h.adj_smul g v z]
    exact hz
  · intro hy
    refine ⟨g⁻¹ • y, ?_, by simp⟩
    show Γ.dist v (g⁻¹ • y) ≤ k
    rw [← IsTree.dist_smul h.isTree h.adj_smul g v (g⁻¹ • y)]
    simpa using hy

theorem stabilizer_le_normalizer_Gm (h : Hyp30 Γ G) (k : ℕ) (v : V) :
    MulAction.stabilizer G v ≤
      Subgroup.normalizer (Gm (Γ := Γ) (G := G) k v : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub g (Gm (Γ := Γ) (G := G) k v) = Gm (Γ := Γ) (G := G) k v
  rw [conjSub_Gm h, MulAction.mem_stabilizer_iff.mp hg]

theorem Gm_le_G1 (h : Hyp30 Γ G) {k : ℕ} {u z : V} (hk : 1 ≤ k)
    (huz : Γ.dist u z ≤ k - 1) :
    Gm (Γ := Γ) (G := G) k u ≤ G1 (Γ := Γ) (G := G) z := by
  intro g hg
  rw [mem_G1]
  constructor
  · rw [mem_Gm] at hg
    exact hg z (by omega)
  · intro y hyz
    rw [mem_Gm] at hg
    have htri := h.isTree.connected.dist_triangle (u := u) (v := z) (w := y)
    rw [dist_eq_one_iff_adj.mpr hyz] at htri
    exact hg y (by omega)

theorem exists_arc_ball_center (hdeg : ∀ u v : V, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v)
    (hex : ∀ u : V, ∃ w, Γ.Adj u w) (hT : Γ.IsTree) (u : V) {k : ℕ} (hk : 1 ≤ k) :
    ∃ R : Arc Γ (2 * k), R.vert k = u ∧ ∀ i, i ≤ 2 * k → Γ.dist u (R.vert i) ≤ k := by
  classical
  obtain ⟨a, ha⟩ := hex u
  obtain ⟨b, hb, hba⟩ := hdeg u a ha
  obtain ⟨A0, hA0⟩ := exists_arc_extend hdeg hex (Arc.step u a ha) k hk
  have hA0_0 : A0.vert 0 = u := by rw [hA0 0 (by omega)]; simp [Arc.step]
  have hA0_1 : A0.vert 1 = a := by rw [hA0 1 le_rfl]; simp [Arc.step]
  let A : Arc Γ k := A0.rev
  have hAk : A.vert k = u := by
    rw [show A.vert k = A0.vert (k - k) from Arc.rev_vert A0 k, Nat.sub_self]
    exact hA0_0
  have hAk1 : A.vert (k - 1) = a := by
    rw [show A.vert (k - 1) = A0.vert (k - (k - 1)) from Arc.rev_vert A0 (k - 1),
      show k - (k - 1) = 1 by omega]
    exact hA0_1
  obtain ⟨B, hB⟩ := exists_arc_extend hdeg hex (Arc.step u b hb) k hk
  have hB0 : B.vert 0 = u := by rw [hB 0 (by omega)]; simp [Arc.step]
  have hB1 : B.vert 1 = b := by rw [hB 1 le_rfl]; simp [Arc.step]
  have hjoin : A.vert k = B.vert 0 := by rw [hAk, hB0]
  have hnb : 1 ≤ k → 1 ≤ k → A.vert (k - 1) ≠ B.vert 1 := by
    intro _ _; rw [hAk1, hB1]; exact hba.symm
  let R : Arc Γ (k + k) := Arc.append A B hjoin hnb
  have hRk : R.vert k = u := by
    rw [show R.vert k = A.vert k from Arc.append_vert_le A B hjoin hnb le_rfl]
    exact hAk
  refine ⟨arcCast (by omega : k + k = 2 * k) R, ?_, ?_⟩
  · rw [arcCast_vert]; exact hRk
  · intro i hi
    rw [arcCast_vert]
    by_cases hik : i ≤ k
    · rw [show R.vert i = A.vert i from Arc.append_vert_le A B hjoin hnb hik]
      have hdist := Arc.dist_vert hT A (i := i) (j := k) hik le_rfl
      rw [hAk, SimpleGraph.dist_comm (u := A.vert i) (v := u)] at hdist
      omega
    · have hik' : k ≤ i := by omega
      rw [Arc.append_vert_ge A B hjoin hnb hik']
      have hdist := Arc.dist_vert hT B (i := 0) (j := i - k) (Nat.zero_le _) (by omega)
      rw [hB0] at hdist
      omega

theorem exists_arc_two_balls (hdeg : ∀ u v : V, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v)
    (hex : ∀ u : V, ∃ w, Γ.Adj u w) (hT : Γ.IsTree) {L : ℕ} (P : Arc Γ L) (hL : 1 ≤ L)
    {k : ℕ} (hk : 1 ≤ k) (hP : ∀ j, j ≤ L → j ≤ k ∨ L - j ≤ k) :
    ∃ R : Arc Γ (L + 2 * k), (∀ i, i ≤ L + 2 * k →
      Γ.dist (P.vert 0) (R.vert i) ≤ k ∨ Γ.dist (P.vert L) (R.vert i) ≤ k) ∧
      (∀ j, j ≤ L → R.vert (k + j) = P.vert j) := by
  classical
  obtain ⟨x, hx, hxne⟩ := hdeg (P.vert 0) (P.vert 1) (P.adj 0 hL)
  obtain ⟨A0, hA0⟩ := exists_arc_extend hdeg hex (Arc.step (P.vert 0) x hx) k hk
  have hA0_0 : A0.vert 0 = P.vert 0 := by rw [hA0 0 (by omega)]; simp [Arc.step]
  have hA0_1 : A0.vert 1 = x := by rw [hA0 1 le_rfl]; simp [Arc.step]
  let A : Arc Γ k := A0.rev
  have hAk : A.vert k = P.vert 0 := by
    rw [show A.vert k = A0.vert (k - k) from Arc.rev_vert A0 k, Nat.sub_self]
    exact hA0_0
  have hAk1 : A.vert (k - 1) = x := by
    rw [show A.vert (k - 1) = A0.vert (k - (k - 1)) from Arc.rev_vert A0 (k - 1),
      show k - (k - 1) = 1 by omega]
    exact hA0_1
  have hjoin1 : A.vert k = P.vert 0 := hAk
  have hnb1 : 1 ≤ k → 1 ≤ L → A.vert (k - 1) ≠ P.vert 1 := by
    intro _ _; rw [hAk1]; exact hxne
  let R1 : Arc Γ (k + L) := Arc.append A P hjoin1 hnb1
  have hR1_left : ∀ i, i ≤ k → R1.vert i = A.vert i :=
    fun i hi => Arc.append_vert_le A P hjoin1 hnb1 hi
  have hR1_mid : ∀ j, j ≤ L → R1.vert (k + j) = P.vert j := by
    intro j hj
    rw [Arc.append_vert_ge A P hjoin1 hnb1 (by omega : k ≤ k + j)]
    congr 1
    omega
  obtain ⟨y, hy, hyne⟩ := hdeg (P.vert L) (P.vert (L - 1)) (by
    have h := (P.adj (L - 1) (by omega)).symm
    rwa [show L - 1 + 1 = L by omega] at h)
  obtain ⟨B, hB⟩ := exists_arc_extend hdeg hex (Arc.step (P.vert L) y hy) k hk
  have hB0 : B.vert 0 = P.vert L := by rw [hB 0 (by omega)]; simp [Arc.step]
  have hB1 : B.vert 1 = y := by rw [hB 1 le_rfl]; simp [Arc.step]
  have hjoin2 : R1.vert (k + L) = B.vert 0 := by
    rw [hR1_mid L le_rfl, hB0]
  have hnb2 : 1 ≤ k + L → 1 ≤ k → R1.vert (k + L - 1) ≠ B.vert 1 := by
    intro _ _
    rw [show k + L - 1 = k + (L - 1) by omega, hR1_mid (L - 1) (by omega), hB1]
    exact hyne.symm
  let R : Arc Γ ((k + L) + k) := Arc.append R1 B hjoin2 hnb2
  refine ⟨arcCast (by omega : (k + L) + k = L + 2 * k) R, ?_, ?_⟩
  · intro i hi
    rw [arcCast_vert]
    by_cases hik : i ≤ k
    · left
      rw [show R.vert i = R1.vert i from Arc.append_vert_le R1 B hjoin2 hnb2 (by omega),
        hR1_left i hik]
      have hdist := Arc.dist_vert hT A (i := i) (j := k) hik le_rfl
      rw [hAk, SimpleGraph.dist_comm (u := A.vert i) (v := P.vert 0)] at hdist
      omega
    · by_cases hile : i ≤ k + L
      · have hik' : k ≤ i := by omega
        rw [show R.vert i = R1.vert i from Arc.append_vert_le R1 B hjoin2 hnb2 (by omega),
          show R1.vert i = P.vert (i - k) from
            Arc.append_vert_ge A P hjoin1 hnb1 hik']
        have hj : i - k ≤ L := by omega
        rcases hP (i - k) hj with hcase | hcase
        · left
          have hdist := Arc.dist_eq hT P (i - k) hj
          omega
        · right
          have hdist := Arc.dist_vert hT P (i := i - k) (j := L) hj le_rfl
          rw [SimpleGraph.dist_comm (u := P.vert (i - k)) (v := P.vert L)] at hdist
          omega
      · right
        have hik' : k + L ≤ i := by omega
        rw [Arc.append_vert_ge R1 B hjoin2 hnb2 hik']
        have hdist := Arc.dist_vert hT B (i := 0) (j := i - (k + L)) (Nat.zero_le _) (by omega)
        rw [hB0] at hdist
        omega
  · intro j hj
    rw [arcCast_vert,
      show R.vert (k + j) = R1.vert (k + j) from
        Arc.append_vert_le R1 B hjoin2 hnb2 (by omega)]
    exact hR1_mid j hj

theorem eq_bot_of_le_G1Set_arc_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {L : ℕ} (R : Arc Γ L) (hL : s - 2 ≤ L) {H : Subgroup G}
    (hH : ∀ i, i ≤ L → H ≤ G1 (Γ := Γ) (G := G) (R.vert i)) : H = ⊥ := by
  have hsub : H ≤ G1Set (Γ := Γ) (G := G) (R.vert '' Set.Icc 0 L) := by
    intro g hg
    rw [mem_G1Set]
    rintro v ⟨i, hi, rfl⟩
    exact hH i (by simpa using hi.2) hg
  have hbot := G1Set_arc_eq_bot_gen h hs hev hs6 T hK (m := L) hL R
  rw [hbot] at hsub
  exact le_bot_iff.mp hsub

theorem eq_bot_of_le_G1Set_arc (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {L : ℕ} (R : Arc Γ L) (hL : s - 2 ≤ L) {H : Subgroup G}
    (hH : ∀ i, i ≤ L → H ≤ G1 (Γ := Γ) (G := G) (R.vert i)) : H = ⊥ :=
  eq_bot_of_le_G1Set_arc_gen h hs hev hs6 T hK R hL hH

theorem even_singularity_far_fixed_false_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y v : V} (hxy : Γ.Adj x y)
    (hfar1 : Γ.dist y v = s / 2 - 1) (hfar2 : Γ.dist x v = s / 2)
    (hZv : centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)) ≤
      G1 (Γ := Γ) (G := G) v) :
    False := by
  classical
  have hev' : Even s := hev
  obtain ⟨t, ht⟩ := hev'
  have hst : s = 2 * t := by omega
  have hs2 : s / 2 = t := by rw [hst, Nat.mul_div_cancel_left t (by norm_num : 0 < 2)]
  have ht3 : 3 ≤ t := by omega
  have hfar1' : Γ.dist y v = t - 1 := by rw [hfar1, hs2]
  have hfar2' : Γ.dist x v = t := by rw [hfar2, hs2]
  let Z : Subgroup G :=
    centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y))
  have hZne : Z ≠ ⊥ := centerOf_pCoreOf_edge_ne_bot h hxy
  have hZle : Z ≤ GmPair (Γ := Γ) (G := G) (t - 1) x y := by
    have h := centerOf_pCoreOf_edge_le_GmPair_gen h hs hev hs6 T hK hQ hxy
    rwa [hs2] at h
  have hZx : Z ≤ Gm (Γ := Γ) (G := G) (t - 1) x := hZle.trans inf_le_left
  have hZy : Z ≤ Gm (Γ := Γ) (G := G) (t - 1) y := hZle.trans inf_le_right
  have hxv : Γ.dist x v = Γ.dist y v + 1 := by rw [hfar1', hfar2']; omega
  have hxvs : Γ.dist x v ≤ s - 2 := by rw [hfar2']; omega
  obtain ⟨Q, hQ0, hQ1, hQv⟩ := exists_arc_through h hxy hxv hxvs
  have hdeg : ∀ u w : V, Γ.Adj u w → ∃ z, Γ.Adj u z ∧ z ≠ w := fun u w _ => h.exists_adj_ne u w
  have hex : ∀ u : V, ∃ z, Γ.Adj u z := h.exists_adj
  obtain ⟨a, ha, ha1⟩ : ∃ a : V, Γ.Adj x a ∧ a ≠ y := h.exists_adj_ne x y
  obtain ⟨A0, hA0⟩ := exists_arc_extend hdeg hex (Arc.step x a ha) (t - 2) (by omega)
  have hA0_0 : A0.vert 0 = x := by rw [hA0 0 (by omega)]; simp [Arc.step]
  have hA0_1 : A0.vert 1 = a := by rw [hA0 1 le_rfl]; simp [Arc.step]
  let A : Arc Γ (t - 2) := A0.rev
  have hAk : A.vert (t - 2) = x := by
    rw [show A.vert (t - 2) = A0.vert ((t - 2) - (t - 2)) from Arc.rev_vert A0 (t - 2),
      Nat.sub_self]
    exact hA0_0
  have hAk1 : A.vert (t - 2 - 1) = a := by
    rw [show A.vert (t - 2 - 1) = A0.vert ((t - 2) - (t - 2 - 1)) from
      Arc.rev_vert A0 (t - 2 - 1), show (t - 2) - (t - 2 - 1) = 1 by omega]
    exact hA0_1
  let Q' : Arc Γ t := initialArc Q t (by omega)
  have hQ'0 : Q'.vert 0 = x := by
    rw [show Q'.vert 0 = Q.vert 0 from initialArc_vert Q t _ 0, hQ0]
  have hQ'1 : Q'.vert 1 = y := by
    rw [show Q'.vert 1 = Q.vert 1 from initialArc_vert Q t _ 1, hQ1]
  have hQ'm : Q'.vert t = v := by
    rw [show Q'.vert t = Q.vert t from initialArc_vert Q t _ t, ← hfar2', hQv]
  have hjoin : A.vert (t - 2) = Q'.vert 0 := by rw [hAk, hQ'0]
  have hnb : 1 ≤ t - 2 → 1 ≤ t → A.vert (t - 2 - 1) ≠ Q'.vert 1 := by
    intro _ _; rw [hAk1, hQ'1]; exact ha1
  let R : Arc Γ (2 * (t - 1)) :=
    arcCast (by omega : (t - 2) + t = 2 * (t - 1)) (Arc.append A Q' hjoin hnb)
  have hdistQ : ∀ j, j ≤ t → Γ.dist x (Q'.vert j) = j := by
    intro j hj
    have h := Arc.dist_eq h.isTree Q' j hj
    rwa [hQ'0] at h
  have hdistQy : ∀ j, 1 ≤ j → j ≤ t → Γ.dist y (Q'.vert j) = j - 1 := by
    intro j hj1 hj2
    have h := Arc.dist_vert h.isTree Q' (i := 1) (j := j) hj1 hj2
    rwa [hQ'1] at h
  have hRfix : ∀ i, i ≤ 2 * (t - 1) → Z ≤ G1 (Γ := Γ) (G := G) (R.vert i) := by
    intro i hi
    rw [show R.vert i = (Arc.append A Q' hjoin hnb).vert i from arcCast_vert _ _ i]
    by_cases hik : i ≤ t - 2
    ·
      rw [show (Arc.append A Q' hjoin hnb).vert i = A.vert i from
        Arc.append_vert_le A Q' hjoin hnb hik]
      have hdist := Arc.dist_vert h.isTree A (i := i) (j := t - 2) hik le_rfl
      rw [hAk, SimpleGraph.dist_comm (u := A.vert i) (v := x)] at hdist
      exact hZx.trans (Gm_le_G1 h (by omega) (by omega))
    ·
      have hik' : t - 2 ≤ i := by omega
      rw [Arc.append_vert_ge A Q' hjoin hnb hik']
      have hjt : i - (t - 2) ≤ t := by omega
      by_cases hj : i - (t - 2) = 0
      · have hx : Q'.vert (i - (t - 2)) = x := by rw [hj, hQ'0]
        rw [hx]
        exact hZx.trans (Gm_le_G1 h (by omega) (by rw [SimpleGraph.dist_self]; omega))
      · by_cases hj1 : i - (t - 2) = 1
        · have hy : Q'.vert (i - (t - 2)) = y := by rw [hj1, hQ'1]
          rw [hy]
          exact hZy.trans (Gm_le_G1 h (by omega) (by rw [SimpleGraph.dist_self]; omega))
        · by_cases hjm : i - (t - 2) = t
          · have : Q'.vert (i - (t - 2)) = v := by rw [hjm]; exact hQ'm
            rw [this]
            exact hZv
          ·
            have hdy : Γ.dist y (Q'.vert (i - (t - 2))) ≤ t - 1 - 1 := by
              rw [hdistQy _ (by omega) hjt]
              omega
            exact hZy.trans (Gm_le_G1 h (by omega) hdy)
  have hZbot : Z = ⊥ :=
    eq_bot_of_le_G1Set_arc_gen h hs hev hs6 T hK R (by omega) hRfix
  exact hZne hZbot

theorem even_singularity_far_fixed_false (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y v : V} (hxy : Γ.Adj x y)
    (hfar1 : Γ.dist y v = s / 2 - 1) (hfar2 : Γ.dist x v = s / 2)
    (hZv : centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)) ≤
      G1 (Γ := Γ) (G := G) v) :
    False :=
  even_singularity_far_fixed_false_gen h hs hev hs6 T hK hQ hxy hfar1 hfar2 hZv

theorem even_singularity_far_moved_false_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y v : V} (hxy : Γ.Adj x y)
    (hfar1 : Γ.dist y v = s / 2 - 1) (hfar2 : Γ.dist x v = s / 2)
    {b : G} (hbZ : b ∈ centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)))
    (hbv : b ∉ G1 (Γ := Γ) (G := G) v) :
    False := by
  classical
  have hev2 : Even s := hev
  obtain ⟨t, ht⟩ := hev2
  have hst : s = 2 * t := by omega
  have hs2 : s / 2 = t := by rw [hst, Nat.mul_div_cancel_left t (by norm_num : 0 < 2)]
  have ht3 : 3 ≤ t := by omega
  have hfar1' : Γ.dist y v = t - 1 := by rw [hfar1, hs2]
  have hfar2' : Γ.dist x v = t := by rw [hfar2, hs2]
  have hdeg : ∀ u w : V, Γ.Adj u w → ∃ z, Γ.Adj u z ∧ z ≠ w := fun u w _ => h.exists_adj_ne u w
  have hex : ∀ u : V, ∃ z, Γ.Adj u z := h.exists_adj
  let Z : Subgroup G :=
    centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y))
  have hZle : Z ≤ GmPair (Γ := Γ) (G := G) (t - 1) x y := by
    have h := centerOf_pCoreOf_edge_le_GmPair_gen h hs hev hs6 T hK hQ hxy
    rwa [hs2] at h
  have hZy : Z ≤ Gm (Γ := Γ) (G := G) (t - 1) y := hZle.trans inf_le_right
  have hbz : b ∈ Gm (Γ := Γ) (G := G) (t - 1) y := hZy hbZ
  have hbv' : b • v = v := by
    rw [mem_Gm] at hbz
    exact hbz v (by rw [hfar1'])
  have hmove : ∃ u, Γ.Adj v u ∧ b • u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hbv (by rw [mem_G1]; exact ⟨hbv', hcon⟩)
  obtain ⟨u, hvu, hbu⟩ := hmove
  have hdyu : Γ.dist y u = t := by
    have hle : Γ.dist y u ≤ t := by
      have h1 : Γ.dist v u = 1 := dist_eq_one_iff_adj.mpr hvu
      have h2 := h.isTree.connected.dist_triangle (u := y) (v := v) (w := u)
      rw [hfar1', h1] at h2
      omega
    by_contra hne
    have hfix : b • u = u := (mem_Gm.mp hbz) u (by omega)
    exact hbu hfix
  let Z' : Subgroup G := centerOf (pCoreOf 2 (MulAction.stabilizer G v ⊓ MulAction.stabilizer G u))
  have hZ'ne : Z' ≠ ⊥ := centerOf_pCoreOf_edge_ne_bot h hvu
  have hZ'le : Z' ≤ GmPair (Γ := Γ) (G := G) (t - 1) v u := by
    have h := centerOf_pCoreOf_edge_le_GmPair_gen h hs hev hs6 T hK hQ hvu
    rwa [hs2] at h
  have hZ'v : Z' ≤ Gm (Γ := Γ) (G := G) (t - 1) v := hZ'le.trans inf_le_left
  have hZ'u : Z' ≤ Gm (Γ := Γ) (G := G) (t - 1) u := hZ'le.trans inf_le_right
  have hcomm : ∀ c ∈ Z', b * c = c * b := by
    intro c hc
    obtain ⟨P, hP0, hPm⟩ := IsTree.exists_arc_between h.isTree y v
    let P' : Arc Γ (t - 1) := arcCast hfar1' P
    have hP'0 : P'.vert 0 = y := by rw [arcCast_vert]; exact hP0
    have hP'L : P'.vert (t - 1) = v := by
      rw [arcCast_vert, ← hfar1']
      exact hPm
    have hP := exists_arc_two_balls hdeg hex h.isTree P' (by omega : 1 ≤ t - 1)
      (by omega : 1 ≤ t - 2)
      (by
        intro j hj
        by_cases h' : j ≤ t - 2
        · exact Or.inl h'
        · exact Or.inr (by omega))
    obtain ⟨R1, hR1ball, -⟩ := hP
    have hcy : c • y = y :=
      mem_Gm.mp (hZ'v hc) y (by rw [SimpleGraph.dist_comm (u := v) (v := y), hfar1'])
    have hK1 : b⁻¹ * c⁻¹ * b * c ∈ Gm (Γ := Γ) (G := G) (t - 1) y := by
      have hstab := stabilizer_le_normalizer_Gm h (t - 1) y hcy
      have hconj : conjSub c (Gm (Γ := Γ) (G := G) (t - 1) y) =
          Gm (Γ := Γ) (G := G) (t - 1) y :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hstab
      have hcbc : c⁻¹ * b * c ∈ Gm (Γ := Γ) (G := G) (t - 1) y := by
        have hmem : b ∈ conjSub c (Gm (Γ := Γ) (G := G) (t - 1) y) := by rw [hconj]; exact hbz
        simpa using (mem_conjSub.mp hmem)
      have := Subgroup.mul_mem (Gm (Γ := Γ) (G := G) (t - 1) y)
        (Subgroup.inv_mem _ hbz) hcbc
      simpa [mul_assoc] using this
    have hK2 : b⁻¹ * c⁻¹ * b * c ∈ Gm (Γ := Γ) (G := G) (t - 1) v := by
      have hbvG : b • v = v := hbv'
      have hstab := stabilizer_le_normalizer_Gm h (t - 1) v hbvG
      have hconj : conjSub b (Gm (Γ := Γ) (G := G) (t - 1) v) =
          Gm (Γ := Γ) (G := G) (t - 1) v :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hstab
      have hcbc : b⁻¹ * c * b ∈ Gm (Γ := Γ) (G := G) (t - 1) v := by
        have hmem : c ∈ conjSub b (Gm (Γ := Γ) (G := G) (t - 1) v) := by
          rw [hconj]; exact hZ'v hc
        simpa using (mem_conjSub.mp hmem)
      have hc' : c ∈ Gm (Γ := Γ) (G := G) (t - 1) v := hZ'v hc
      have h := Subgroup.mul_mem (Gm (Γ := Γ) (G := G) (t - 1) v)
        (Subgroup.inv_mem _ hcbc) hc'
      simpa [mul_assoc] using h
    have hKm : b⁻¹ * c⁻¹ * b * c ∈
        G1Set (Γ := Γ) (G := G) (R1.vert '' Set.Icc 0 ((t - 1) + 2 * (t - 2))) := by
      rw [mem_G1Set]
      rintro z ⟨i, hi, rfl⟩
      have hi' : i ≤ (t - 1) + 2 * (t - 2) := by
        have h := hi.2
        omega
      rcases hR1ball i hi' with hball | hball
      · rw [hP'0] at hball
        exact (Gm_le_G1 h (by omega) (by omega)) hK1
      · rw [hP'L] at hball
        exact (Gm_le_G1 h (by omega) (by omega)) hK2
    have hbot : G1Set (Γ := Γ) (G := G) (R1.vert '' Set.Icc 0 ((t - 1) + 2 * (t - 2))) = ⊥ :=
      G1Set_arc_eq_bot_gen h hs hev hs6 T hK (m := (t - 1) + 2 * (t - 2))
        (by rw [hst]; omega) R1
    rw [hbot] at hKm
    have hK1' : b⁻¹ * c⁻¹ * b * c = 1 := by simpa using hKm
    have hcbc : c⁻¹ * b * c = b := by
      have h := congrArg (fun x => b * x) hK1'
      simpa [mul_assoc] using h
    have : b * c = c * b := by
      have h := congrArg (fun x => c * x) hcbc
      simpa [mul_assoc] using h
    exact this
  have hZ'w : Z' ≤ Gm (Γ := Γ) (G := G) (t - 1) (b • u) := by
    intro c hc
    rw [mem_Gm]
    intro z hz
    have h1 : Γ.dist u (b⁻¹ • z) ≤ t - 1 := by
      rw [← IsTree.dist_smul h.isTree h.adj_smul b u (b⁻¹ • z)]
      simpa using hz
    have h2 : c • (b⁻¹ • z) = b⁻¹ • z := (mem_Gm.mp (hZ'u hc)) _ h1
    have hcomm' : c * b = b * c := (hcomm c hc).symm
    calc c • z = c • (b • (b⁻¹ • z)) := by rw [smul_inv_smul]
      _ = (c * b) • (b⁻¹ • z) := by rw [mul_smul]
      _ = (b * c) • (b⁻¹ • z) := by rw [hcomm']
      _ = b • (c • (b⁻¹ • z)) := by rw [mul_smul]
      _ = b • (b⁻¹ • z) := by rw [h2]
      _ = z := by rw [smul_inv_smul]
  have hbvw : Γ.Adj v (b • u) := by
    have h' := (h.adj_smul b v u).2 hvu
    rwa [hbv'] at h'
  have huw : b • u ≠ u := hbu
  let P : Arc Γ 2 := snocArc (Arc.step u v hvu.symm) (b • u) hbvw (fun _ => huw)
  have hP0 : P.vert 0 = u := by simp [P, snocArc_vert_le, Arc.step]
  have hP2 : P.vert 2 = b • u := by simp [P, snocArc_vert_last, Arc.step]
  have hP := exists_arc_two_balls hdeg hex h.isTree P (by norm_num : 1 ≤ 2)
    (by omega : 1 ≤ t - 2)
    (by
      intro j hj
      interval_cases j
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
  obtain ⟨R2, hR2ball, -⟩ := hP
  have hZ'bot : Z' = ⊥ := by
    refine eq_bot_of_le_G1Set_arc_gen h hs hev hs6 T hK R2 ?_ ?_
    · rw [hst]
      omega
    · intro i hi
      have hi' : i ≤ 2 + 2 * (t - 2) := by
        have h := hi
        omega
      rcases hR2ball i hi' with hball | hball
      · rw [hP0] at hball
        exact hZ'u.trans (Gm_le_G1 h (by omega) (by omega))
      · rw [hP2] at hball
        exact hZ'w.trans (Gm_le_G1 h (by omega) (by omega))
  exact hZ'ne hZ'bot

theorem even_singularity_far_moved_false (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v)
    {x y v : V} (hxy : Γ.Adj x y)
    (hfar1 : Γ.dist y v = s / 2 - 1) (hfar2 : Γ.dist x v = s / 2)
    {b : G} (hbZ : b ∈ centerOf (pCoreOf 2 (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)))
    (hbv : b ∉ G1 (Γ := Γ) (G := G) v) :
    False :=
  even_singularity_far_moved_false_gen h hs hev hs6 T hK hQ hxy hfar1 hfar2 hbZ hbv

theorem even_singularity_ge_six_false_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v) :
    False := by
  classical
  set x : V := T.line.vert 0
  set y : V := T.line.vert 1
  have hxy : Γ.Adj x y := T.line.adj 0
  have hdeg : ∀ u w : V, Γ.Adj u w → ∃ z, Γ.Adj u z ∧ z ≠ w := fun u w _ => h.exists_adj_ne u w
  have hex : ∀ u : V, ∃ z, Γ.Adj u z := h.exists_adj
  obtain ⟨Q, hQarc⟩ := exists_arc_extend hdeg hex (Arc.step x y hxy) (s - 1) (by omega)
  have hQ0 : Q.vert 0 = x := by rw [hQarc 0 (by omega)]; simp [Arc.step]
  have hQ1 : Q.vert 1 = y := by rw [hQarc 1 le_rfl]; simp [Arc.step]
  have hs2le : s / 2 ≤ s - 1 := by omega
  have hfar1 : Γ.dist y (Q.vert (s / 2)) = s / 2 - 1 := by
    have h := Arc.dist_vert h.isTree Q (i := 1) (j := s / 2) (by omega) hs2le
    rwa [hQ1] at h
  have hfar2 : Γ.dist x (Q.vert (s / 2)) = s / 2 := by
    have h := Arc.dist_eq h.isTree Q (s / 2) hs2le
    rwa [hQ0] at h
  by_cases hA : centerOf (pCoreOf 2
      (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)) ≤
      G1 (Γ := Γ) (G := G) (Q.vert (s / 2))
  · exact even_singularity_far_fixed_false_gen h hs hev hs6 T hK hQ hxy hfar1 hfar2 hA
  · have hex' : ∃ b : G, b ∈ centerOf (pCoreOf 2
        (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)) ∧
        b ∉ G1 (Γ := Γ) (G := G) (Q.vert (s / 2)) := by
      by_contra hcon
      apply hA
      intro b hb
      by_contra hb1
      exact hcon ⟨b, hb, hb1⟩
    obtain ⟨b, hbZ, hbv⟩ := hex'
    exact even_singularity_far_moved_false_gen h hs hev hs6 T hK hQ hxy hfar1 hfar2 hbZ hbv

theorem even_singularity_ge_six_false (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v) :
    False :=
  even_singularity_ge_six_false_gen h hs hev hs6 T hK hQ

theorem singularity_le_four_of_even_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v) :
    s ≤ 4 := by
  by_contra hle
  have hs6 : 6 ≤ s := by
    obtain ⟨t, ht⟩ := hev
    omega
  exact even_singularity_ge_six_false_gen h hs hev hs6 T hK hQ

theorem singularity_le_four_of_even (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hQ : ∀ (v : V) (P : Subgroup G), IsPGroup 2 P → P ≤ MulAction.stabilizer G v →
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → (∀ g ∈ P, g • a = a) →
        (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v) :
    s ≤ 4 :=
  singularity_le_four_of_even_gen h hs hev T hK hQ

end CFSG.Quasithin.St84
