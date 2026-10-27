module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2Core
public import CFSG.RankThree.PartTwo.Sec13.K135OutPCore
public import CFSG.Quasithin.H13.NQCoreP134Group
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSU
public import CFSG.RankThree.PartTwo.Sec13.KF135Core
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcBasic

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2

open CFSG.RankThree.PartOne.OutStructure (OutPChain)

@[expose] def H2bFor (G : Type*) [Group G] (p : ℕ) (P : Subgroup (MulAut G)) : Prop :=
  ∀ F : Subgroup (MulAut G), F ≤ P → CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
    ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup 2 U → ∃ φ ∈ F, U.map φ.toMonoidHom ≠ U

theorem H2bFor.map_congr {G G' : Type} [Group G] [Group G'] {p : ℕ} {P : Subgroup (MulAut G)}
    (hP : H2bFor G p P) (ε : G ≃* G') :
    H2bFor G' p (P.map (MulAut.congr ε).toMonoidHom) := by
  intro F' hF'P hF'ab hF'c U hU hU2
  set F := F'.map (MulAut.congr ε).symm.toMonoidHom with hF
  have hFP : F ≤ P := by
    rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hF'P hφ'
    change (MulAut.congr ε).symm ((MulAut.congr ε) φ) ∈ P
    rw [MulEquiv.symm_apply_apply]
    exact hφ
  have hFab : CFSG.Open.IsElemAbelian p F := CFSG.Open.IsElemAbelian.map hF'ab _
  have hFc : Nat.card F = p ^ 2 := by
    rw [hF, Subgroup.card_map_of_injective (MulAut.congr ε).symm.injective]
    exact hF'c
  set U₀ := U.map ε.symm.toMonoidHom with hU₀
  have hU₀1 : U₀ ≠ ⊥ := by
    intro h0
    apply hU
    rw [eq_bot_iff]
    intro y hy
    have : ε.symm y ∈ U₀ := ⟨y, hy, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    simpa using congrArg ε this
  obtain ⟨φ, hφF, hne⟩ := hP F hFP hFab hFc U₀ hU₀1 (hU2.map _)
  obtain ⟨φ', hφ', rfl⟩ := hφF
  refine ⟨φ', hφ', fun heq => hne ?_⟩
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : φ' w ∈ U := heq ▸ ⟨w, hw, rfl⟩
    refine ⟨φ' w, hw', ?_⟩
    simp [MulAut.congr_apply]
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ U.map φ'.toMonoidHom := heq.symm ▸ hw
    obtain ⟨z, hz, hzw⟩ := hw'
    refine ⟨ε.symm z, ⟨z, hz, rfl⟩, ?_⟩
    simp [MulAut.congr_apply, ← hzw]

theorem exists_sylow_map_eq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup (MulAut G)} (hP : IsPGroup p P) :
    ∃ Q : Sylow p G, ∀ φ ∈ P, (Q : Subgroup G).map φ.toMonoidHom = Q := by
  obtain ⟨Q, hQ⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p G)
    (not_dvd_card_sylow p G)
  refine ⟨Q, fun φ hφ => ?_⟩
  have h1 : (⟨φ, hφ⟩ : P) • Q = Q := hQ ⟨φ, hφ⟩
  have h2 : φ • Q = Q := (Subgroup.smul_def (⟨φ, hφ⟩ : P) Q).symm.trans h1
  have h3 := congrArg (fun Q' : Sylow p G => (Q' : Subgroup G)) h2
  simp only [Sylow.pointwise_smul_def] at h3
  rw [← CFSG.RankThree.PartTwo.Sec13.KF135Proof.smul_subgroup_eq_map]
  exact h3

theorem mem_of_conj_mem {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (Q : Sylow p G)
    {t : G} (ht : t ^ p = 1)
    (hQ : (Q : Subgroup G).map (MulAut.conj t).toMonoidHom = Q) : t ∈ Q := by
  classical
  have hzp : IsPGroup p (Subgroup.zpowers t) := IsPGroup.of_card (n := if t = 1 then 0 else 1)
    (by
      rw [Nat.card_zpowers]
      split_ifs with h1
      · rw [h1, orderOf_one, pow_zero]
      · rw [pow_one]
        exact orderOf_eq_prime ht h1)
  have htN : t ∈ Subgroup.normalizer (((Q : Subgroup G) : Set G)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hQ
  have := hzp.inf_normalizer_sylow Q
  have hmem : t ∈ Subgroup.zpowers t ⊓ Subgroup.normalizer (((Q : Subgroup G) : Set G)) :=
    ⟨Subgroup.mem_zpowers t, htN⟩
  have hmem' : t ∈ Subgroup.zpowers t ⊓ (Q : Subgroup G) := by
    rw [← this]
    exact hmem
  exact hmem'.2

theorem sq_le_card_inf_inner {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hout : OutPChain p G) {P : Subgroup (MulAut G)} (hexp : ∀ y ∈ P, y ^ p = 1)
    (hcard : p ^ 3 ≤ Nat.card P) :
    p ^ 2 ≤ Nat.card (P ⊓ (MulAut.conj : G →* MulAut G).range : Subgroup (MulAut G)) := by
  set A := P ⊓ (MulAut.conj : G →* MulAut G).range with hA
  have hidx : A.relIndex P ≤ p :=
    CFSG.RankThree.PartTwo.Sec13.F135Last.relIndex_le_of_outPChain hp hout P hexp
  have h1 : Nat.card A * A.relIndex P = Nat.card P := by
    have e := (A.subgroupOf P).card_mul_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ≤ P)).toEquiv] at e
  have hpos : 0 < p := hp.pos
  by_contra hlt
  push Not at hlt
  have h2 : Nat.card A * A.relIndex P < p ^ 2 * p := Nat.mul_lt_mul_of_lt_of_le hlt hidx hpos
  rw [h1] at h2
  have h3 : p ^ 2 * p = p ^ 3 := by ring
  omega

theorem conj_injective_of_simple {G : Type} [Group G] (hG : IsSimpleGroup G)
    (hnab : ¬ ∀ a b : G, a * b = b * a) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAut.conj : G →* MulAut G).ker with hk | hk
  · exact hk
  · exfalso
    apply hnab
    intro a b
    have hb : MulAut.conj b = 1 := (MonoidHom.mem_ker).mp (hk ▸ Subgroup.mem_top b)
    have := congrArg (fun φ : MulAut G => φ a) hb
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc a * b = b * a * b⁻¹ * b := by rw [this]
      _ = b * a := by group

theorem false_of_fixed_commute {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    {P : Subgroup (MulAut G)} (hexp : ∀ y ∈ P, y ^ p = 1) (h2b : H2bFor G p P)
    {a : MulAut G} (haP : a ∈ P) (haI : a ∉ (MulAut.conj : G →* MulAut G).range)
    {t : G} (htP : MulAut.conj t ∈ P) (ht1 : t ≠ 1) (hat : a t = t)
    {s : G} (hs1 : s ≠ 1) (hs2 : s * s = 1) (has : a s = s) (hts : t * s = s * t) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c := MulAut.conj t with hc
  have hac : a * c = c * a := by
    ext y
    simp only [hc, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hat]
  set F₀ := Subgroup.closure ({a, c} : Set (MulAut G)) with hF₀
  have hF₀P : F₀ ≤ P := (Subgroup.closure_le P).2 (by
    rintro _ (rfl | rfl)
    · exact haP
    · exact htP)
  obtain ⟨hF₀c, hF₀p⟩ := CFSG.StandardType.OrdPNsU.closure_comm_pow
    (S := ({a, c} : Set (MulAut G))) (p := p)
    (by
      rintro x (rfl | rfl) y (rfl | rfl)
      · rfl
      · exact hac
      · exact hac.symm
      · rfl)
    (by
      rintro x (rfl | rfl)
      · exact hexp _ haP
      · exact hexp _ htP)
  have hfix : ∀ φ ∈ F₀, φ s = s := by
    intro φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact has
      · change t * s * t⁻¹ = s
        rw [hts, mul_inv_cancel_right]
    | one => rfl
    | mul x y _ _ hx hy => rw [MulAut.mul_apply, hy, hx]
    | inv x _ hx =>
      calc x⁻¹ s = x⁻¹ (x s) := by rw [hx]
        _ = s := by simp
  have hzp : orderOf a = p := orderOf_eq_prime (hexp a haP)
    (fun h1 => haI (h1 ▸ Subgroup.one_mem _))
  have hza : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hzp]
  have hcnot : c ∉ Subgroup.zpowers a := by
    intro hcz
    set I := Subgroup.zpowers a ⊓ (MulAut.conj : G →* MulAut G).range with hI
    have hdvd : Nat.card I ∣ p := hza ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · have : c ∈ I := ⟨hcz, ⟨t, rfl⟩⟩
      rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot] at this
      exact ht1 (hinj (by rw [map_one]; exact this))
    · have hle : I = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hza, h1])
      have : a ∈ I := hle ▸ Subgroup.mem_zpowers a
      exact haI this.2
  have hlt : Subgroup.zpowers a < F₀ := by
    refine lt_of_le_of_ne ?_ fun h => hcnot (h ▸ Subgroup.subset_closure (Or.inr rfl))
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Or.inl rfl)
  have hF₀pg : IsPGroup p F₀ := fun g => ⟨1, Subtype.ext (by simpa using hF₀p g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hF₀pg
  have hcardlt : p < Nat.card F₀ := hza ▸ Subgroup.card_lt_of_lt hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have : k ≤ 1 := by omega
    have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
    rw [pow_one, ← hk] at this
    omega
  have hcard2 : p ^ 2 ≤ Nat.card F₀ := hk ▸ Nat.pow_le_pow_right hp.pos hk2
  obtain ⟨E, hEF₀, hEab, hEc⟩ := CFSG.Quasithin.H13.NQCore.exists_elemAbelian_sq hF₀p hcard2
  have hso : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  have hU2 : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hso, pow_one])
  have hU1 : Subgroup.zpowers s ≠ ⊥ := by
    intro h0
    have : s ∈ (⊥ : Subgroup G) := h0 ▸ Subgroup.mem_zpowers s
    exact hs1 (Subgroup.mem_bot.1 this)
  obtain ⟨φ, hφE, hne⟩ := h2b E (hEF₀.trans hF₀P) hEab hEc _ hU1 hU2
  apply hne
  rw [MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers (hfix φ (hEF₀ hφE))

theorem false_of_e2_core {T : Type} [Group T] [Finite T] {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (hshape : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e T) (he : 2 ≤ e)
    (hout : OutPChain p T) {P : Subgroup (MulAut T)} (hP : IsPGroup p P)
    (hexp : ∀ y ∈ P, y ^ p = 1) (hcard : p ^ 3 ≤ Nat.card P) (h2b : H2bFor T p P)
    {a : MulAut T} (haP : a ∈ P) (haI : a ∉ (MulAut.conj : T →* MulAut T).range)
    (hinv : ∀ B : Subgroup T, CFSG.Open.IsElemAbelian p B → p ^ 2 ≤ Nat.card B →
      (∀ t ∈ B, a t = t) → ∃ t ∈ B, t ≠ 1 ∧ ∃ s : T, s ≠ 1 ∧ s * s = 1 ∧ a s = s ∧
        t * s = s * t) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  set A := P ⊓ (MulAut.conj : T →* MulAut T).range with hA
  have hAcard : p ^ 2 ≤ Nat.card A := sq_le_card_inf_inner hp hout hexp hcard
  obtain ⟨Q, hQ⟩ := exists_sylow_map_eq hP
  obtain ⟨eQ⟩ := hshape Q Q.isPGroup' Q.not_dvd_index
  set B := A.comap (MulAut.conj : T →* MulAut T) with hB
  have hBcard : p ^ 2 ≤ Nat.card B := by
    rw [hB, KF135Chev2Exc.card_comap_conj hinj inf_le_right]
    exact hAcard
  have hBp : ∀ t ∈ B, t ^ p = 1 := fun t ht => hinj (by
    rw [map_pow, map_one]
    exact hexp _ ht.1)
  have hBQ : ∀ t ∈ B, t ∈ Q := fun t ht => mem_of_conj_mem Q (hBp t ht) (hQ _ ht.1)
  have haB : ∀ t ∈ B, a t = t := fun t ht =>
    aut_trivial_mod_p_of_homocyclic hp5 (Or.inr rfl) he eQ a (hQ a haP) (hexp a haP)
      (hBQ t ht) (hBp t ht)
  have hQab : ∀ x ∈ (Q : Subgroup T), ∀ y ∈ (Q : Subgroup T), x * y = y * x :=
    fun x hx y hy => by
      have := KF135Chev2Exc.isMulCommutative_of_sylowShape hshape Q
      exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBab : CFSG.Open.IsElemAbelian p B :=
    ⟨⟨⟨fun x y => Subtype.ext (hQab _ (hBQ _ x.2) _ (hBQ _ y.2))⟩⟩, hBp⟩
  obtain ⟨t, htB, ht1, s, hs1, hs2, has, hts⟩ := hinv B hBab hBcard haB
  exact false_of_fixed_commute hp hinj hexp h2b haP haI htB.1 ht1 (haB t htB) hs1 hs2 has hts

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2
