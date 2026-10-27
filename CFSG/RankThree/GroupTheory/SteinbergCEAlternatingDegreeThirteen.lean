module

public import CFSG.Foundations.Basic
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXAlternatingThreeCycles
import CFSG.LocalAnalysis.SectionRank.AlternatingCover
import CFSG.Milestones.LC_GL_local_rank_bounds
import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.GroupTheory

open Equiv Equiv.Perm Subgroup

@[expose] def thirteenKleinX : Perm (Fin 13) := swap 0 1 * swap 2 3

@[expose] def thirteenKleinY : Perm (Fin 13) := swap 0 2 * swap 1 3

@[expose] def thirteenCycle : Fin 4 → Perm (Fin 13) :=
  ![swap 0 1 * swap 0 2, swap 4 5 * swap 4 6, swap 7 8 * swap 7 9, swap 10 11 * swap 10 12]

theorem thirteenKleinX_sign : sign thirteenKleinX = 1 := by decide +kernel

theorem thirteenKleinY_sign : sign thirteenKleinY = 1 := by decide +kernel

theorem thirteenCycle_isThreeCycle (i : Fin 4) : (thirteenCycle i).IsThreeCycle := by
  fin_cases i <;> exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem thirteenCycle_disjoint : Pairwise fun i j : Fin 4 => (thirteenCycle i).Disjoint
    (thirteenCycle j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (intro x; fin_cases x <;> decide)

theorem thirteenCycle_zero_conj_x :
    thirteenCycle 0 * thirteenKleinX * (thirteenCycle 0)⁻¹ = thirteenKleinY := by decide +kernel

theorem thirteenCycle_zero_conj_y :
    thirteenCycle 0 * thirteenKleinY * (thirteenCycle 0)⁻¹ = thirteenKleinX * thirteenKleinY := by
  decide +kernel

theorem thirteenCycle_commute_x : ∀ i : Fin 4, i ≠ 0 →
    thirteenCycle i * thirteenKleinX = thirteenKleinX * thirteenCycle i := by decide +kernel

theorem thirteenCycle_commute_y : ∀ i : Fin 4, i ≠ 0 →
    thirteenCycle i * thirteenKleinY = thirteenKleinY * thirteenCycle i := by decide +kernel

theorem thirteenKlein_commute : thirteenKleinX * thirteenKleinY = thirteenKleinY * thirteenKleinX :=
  by decide +kernel

theorem thirteenKleinX_ne_one : thirteenKleinX ≠ 1 := by decide +kernel

theorem thirteenKleinX_mul_self : thirteenKleinX * thirteenKleinX = 1 := by decide +kernel

theorem mem_normalizer_closure_of_conj_mem {G : Type*} [Group G] [Finite G] {S : Set G} {g : G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  set H := Subgroup.closure S
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  have heq : H.map (MulAut.conj g).toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem : (MulAut.conj g) x ∈ H.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [heq] at hmem
    simpa using hmem
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    rwa [← hxy]

theorem normalizer_le_normalizer_map_subtype {G : Type*} [Group G] {F : Subgroup G}
    (C : Subgroup F) [hC : C.Characteristic] :
    Subgroup.normalizer (F : Set G) ≤
      Subgroup.normalizer ((C.map F.subtype : Subgroup G) : Set G) := by
  intro g hg
  set φ := F.normalizerMonoidHom ⟨g, hg⟩
  have hφ : C.comap φ.toMonoidHom = C := Subgroup.characteristic_iff_comap_eq.mp hC φ
  have hφg : ∀ f : F, ((φ f : F) : G) = g * f * g⁻¹ := fun f =>
    Subgroup.normalizerMonoidHom_apply_apply_coe F ⟨g, hg⟩ f
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨φ c, ?_, hφg c⟩
    have hc' : c ∈ C.comap φ.toMonoidHom := hφ.symm ▸ hc
    exact hc'
  · rintro ⟨c, hc, hcx⟩
    have hxF : x ∈ F := by
      have h := (Subgroup.mem_normalizer_iff.mp hg x).mpr
      apply h
      rw [← hcx]
      exact c.2
    refine ⟨⟨x, hxF⟩, ?_, rfl⟩
    have hφx : φ ⟨x, hxF⟩ = c := Subtype.ext (by rw [hφg]; exact hcx.symm)
    have hmem : (⟨x, hxF⟩ : F) ∈ C.comap φ.toMonoidHom := by
      change φ ⟨x, hxF⟩ ∈ C
      rw [hφx]
      exact hc
    rwa [hφ] at hmem

theorem pCore_two_ne_bot_of_isNilpotent {W : Type*} [Group W] [Finite W]
    (hW : Group.IsNilpotent W) (h2 : 2 ∣ Nat.card W) : CFSG.pCore 2 W ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain P : Sylow 2 W := default
  have hPn : (P : Subgroup W).Normal := Group.IsNilpotent.sylow_normal hW 2 P
  have hle : (P : Subgroup W) ≤ CFSG.pCore 2 W := le_sSup ⟨hPn, P.isPGroup'⟩
  exact fun h => Sylow.ne_bot_of_dvd_card P h2 (le_bot_iff.mp (h ▸ hle))

open CFSG.Assembly.RankThreeEven (localRank) in
theorem alternating_central_covers_degree_thirteen_force_two_local_three_rank_four
    {G : Type*} [Group G] [Finite G] {K : Subgroup G} {n : ℕ}
    (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center K) :
    (13 ≤ n → ∃ U V : Subgroup G, U ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        V ≤ K ⊓ Subgroup.normalizer (U : Set G) ∧ CFSG.IsElementaryAbelian 3 V ∧
        Nat.card V = 3 ^ 4) ∧
      (13 ≤ n → 4 ≤ localRank 3 G ∧ 4 ≤ CFSG.twoLocalOddRank G ∧
        4 ≤ CFSG.Assembly.evenRank G) ∧
      (CFSG.twoLocalOddRank G ≤ 3 → n ≤ 12) ∧ (CFSG.Assembly.evenRank G ≤ 3 → n ≤ 12) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hex : 13 ≤ n → ∃ U V : Subgroup G, U ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      V ≤ K ⊓ Subgroup.normalizer (U : Set G) ∧ CFSG.IsElementaryAbelian 3 V ∧
      Nat.card V = 3 ^ 4 := by
    intro hn
    set ι := CFSG.SectionRank.altEmbed hn
    set x : alternatingGroup (Fin 13) := ⟨thirteenKleinX, thirteenKleinX_sign⟩
    set y : alternatingGroup (Fin 13) := ⟨thirteenKleinY, thirteenKleinY_sign⟩
    set c₀ : Fin 4 → alternatingGroup (Fin 13) := fun i =>
      ⟨thirteenCycle i, (thirteenCycle_isThreeCycle i).mem_alternatingGroup⟩
    set Q₀ := Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 13)))
    have hxy : x * y = y * x := Subtype.ext thirteenKlein_commute
    have hnorm₀ : ∀ i, c₀ i ∈ Subgroup.normalizer (Q₀ : Set (alternatingGroup (Fin 13))) := by
      intro i
      apply mem_normalizer_closure_of_conj_mem
      have hx : x ∈ Q₀ := Subgroup.subset_closure (by simp)
      have hy : y ∈ Q₀ := Subgroup.subset_closure (by simp)
      rintro s (rfl | rfl)
      · by_cases hi : i = 0
        · subst hi
          have h : c₀ 0 * x * (c₀ 0)⁻¹ = y := Subtype.ext thirteenCycle_zero_conj_x
          rw [h]
          exact hy
        · have h : c₀ i * x = x * c₀ i := Subtype.ext (thirteenCycle_commute_x i hi)
          rw [h, mul_inv_cancel_right]
          exact hx
      · by_cases hi : i = 0
        · subst hi
          have h : c₀ 0 * y * (c₀ 0)⁻¹ = x * y := Subtype.ext thirteenCycle_zero_conj_y
          rw [h]
          exact Q₀.mul_mem hx hy
        · have h : c₀ i * y = y * c₀ i := Subtype.ext (thirteenCycle_commute_y i hi)
          rw [h, mul_inv_cancel_right]
          exact hy
    set Q := Q₀.map ι
    set c : Fin 4 → alternatingGroup (Fin n) := fun i => ι (c₀ i)
    have hc3 : ∀ i, (c i : Perm (Fin n)).IsThreeCycle := fun i => by
      change ((thirteenCycle i).extendDomain (CFSG.SectionRank.firstPts hn)).cycleType = {3}
      rw [cycleType_extendDomain]
      exact thirteenCycle_isThreeCycle i
    have hcd : Pairwise fun i j => (c i : Perm (Fin n)).Disjoint (c j) := fun i j hij =>
      (thirteenCycle_disjoint hij).extendDomain (CFSG.SectionRank.firstPts hn)
    have hcQ : Subgroup.closure (Set.range c) ≤ Subgroup.normalizer (Q : Set (alternatingGroup
        (Fin n))) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι (hnorm₀ i))
    obtain ⟨-, ⟨V, hVel, hVcard, -, hVmap⟩, -⟩ :=
      LocalAnalysis.GorensteinLyons.alternating_central_cover_injective_disjoint_three_cycles.{0}
        (k := 4) (by norm_num) (by omega) π hπ hZ c hc3 hcd
    set F := Q.comap π
    have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
      have hQ₀ : IsMulCommutative Q₀ := Subgroup.isMulCommutative_closure (by
        rintro a (rfl | rfl) b (rfl | rfl) - <;> first | rfl | exact hxy | exact hxy.symm)
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ι (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Q₀) ⟨b, hb⟩))
    let f : F →* Q := (π.comp F.subtype).codRestrict Q fun w => w.2
    have hf : Function.Surjective f := by
      rintro ⟨q, hq⟩
      obtain ⟨w, rfl⟩ := hπ q
      exact ⟨⟨w, hq⟩, rfl⟩
    have hfker : f.ker ≤ Subgroup.center F := by
      intro w hw
      have hwK : (w : K) ∈ π.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hw)
      exact Subgroup.mem_center_iff.mpr fun w' =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hZ hwK) w')
    have : IsMulCommutative Q := ⟨⟨fun a b => Subtype.ext (hQab a a.2 b b.2)⟩⟩
    have hFnil : Group.IsNilpotent F := Subgroup.isNilpotent_of_ker_le_center f hfker
    have hF2 : 2 ∣ Nat.card F := by
      have hxQ : ι x ∈ Q := Subgroup.mem_map_of_mem ι (Subgroup.subset_closure (by simp))
      have hord : orderOf (⟨ι x, hxQ⟩ : Q) = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        apply orderOf_eq_prime
        · apply Subtype.ext
          change ι x ^ 2 = 1
          rw [← map_pow, pow_two]
          have h : x * x = 1 := Subtype.ext thirteenKleinX_mul_self
          rw [h, map_one]
        · intro h
          have h1 : ι x = 1 := congrArg Subtype.val h
          have h2 : x = 1 := CFSG.SectionRank.altEmbed_injective hn (h1.trans (map_one ι).symm)
          exact thirteenKleinX_ne_one (congrArg Subtype.val h2)
      exact (hord ▸ _root_.orderOf_dvd_natCard _).trans (Subgroup.card_dvd_of_surjective hf)
    set U₀ := (CFSG.pCore 2 F).map F.subtype
    have hU₀ : CFSG.pCore 2 F ≠ ⊥ := pCore_two_ne_bot_of_isNilpotent hFnil hF2
    have hVF : V ≤ Subgroup.normalizer (F : Set K) := by
      intro v hv
      apply Subgroup.le_normalizer_comap π
      rw [Subgroup.mem_comap]
      exact hcQ (hVmap ▸ Subgroup.mem_map_of_mem π hv)
    have hVU : V ≤ Subgroup.normalizer (U₀ : Set K) :=
      hVF.trans (normalizer_le_normalizer_map_subtype (CFSG.pCore 2 F))
    refine ⟨U₀.map K.subtype, V.map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_,
      CFSG.IsElementaryAbelian.map_subtype, ?_⟩
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective,
        Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective]
      exact hU₀
    · have h2 : IsPGroup 2 (CFSG.pCore 2 F) := CFSG.pCore_isPGroup
      exact (h2.map F.subtype).map K.subtype
    · exact le_inf (Subgroup.map_subtype_le _)
        ((Subgroup.map_mono hVU).trans (Subgroup.le_normalizer_map K.subtype))
    · rw [Subgroup.card_map_of_injective K.subtype_injective, hVcard]
  have hrank : 13 ≤ n → 4 ≤ localRank 3 G ∧ 4 ≤ CFSG.twoLocalOddRank G ∧
      4 ≤ CFSG.Assembly.evenRank G := by
    intro hn
    obtain ⟨U, V, -, hU1, hU2, hVle, hVel, hVcard⟩ := hex hn
    have h3 : 4 ≤ localRank 3 G :=
      CFSG.RankThree.Theta.le_localRank_of_le_normalizer (by norm_num) hU1 hU2
        hVel.toIsMulCommutative (fun w hw => CFSG.elemPow_eq_one_of_isElementaryAbelian w hw)
        hVcard (hVle.trans inf_le_right)
    have h3G : 3 ∣ Nat.card G :=
      (Dvd.intro_left _ (hVcard.symm.trans (by norm_num))).trans (Subgroup.card_subgroup_dvd_card V)
    refine ⟨h3, h3.trans
      (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank Nat.prime_three (by norm_num) h3G), ?_⟩
    exact h3.trans ((CFSG.Milestones.lc_gl_local_rank_bounds G).1 3 Nat.prime_three
      (by norm_num)).2
  refine ⟨hex, hrank, fun h => ?_, fun h => ?_⟩
  · by_contra hn
    have := (hrank (by omega)).2.1
    omega
  · by_contra hn
    have := (hrank (by omega)).2.2
    omega

end CFSG.RankThree.GroupTheory
