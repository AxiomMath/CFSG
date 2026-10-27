module

public import CFSG.RankThree.PartOne.KFOUT3.K2Std
public import CFSG.RankThree.PartOne.KFOUT3.LemmaF

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143 CFSG.Assembly.LowTwoRank

section Aux

variable {G : Type} [Group G] {J : Subgroup G} {K : Type} [Field K]

theorem conjAut_mul_of_eq (ι : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K) {u v z : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (hv : v ∈ Subgroup.normalizer (J : Set G))
    (h : u * v = z) (hz : z ∈ Subgroup.normalizer (J : Set G)) :
    conjAut ι hz = conjAut ι hu * conjAut ι hv := by
  subst h
  ext x
  obtain ⟨y, rfl⟩ := ι.surjective x
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAut.mul_apply, conjAut_apply, conjAut_apply, conjAut_apply]
  congr 2
  apply Subtype.ext
  simp [jConj_apply, mul_assoc]

omit [Field K] in
theorem Tof_conj_mem {A : Subgroup G} {x : G} (hxJ : x ∈ Subgroup.normalizer (J : Set G))
    (hxW : x ∈ torusNormalizer A) {t : G} (ht : t ∈ Tof A J) : x * t * x⁻¹ ∈ Tof A J := by
  have hle : Tof A J ≤ (Tof A J).comap (MulAut.conj x).toMonoidHom := by
    rw [Tof, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement]
    apply Subgroup.commutator_mem_commutator
    · rw [MulAut.conj_apply]
      exact (Subgroup.mem_normalizer_iff.1 hxW a).1 ha
    · refine ⟨?_, ?_⟩
      · rw [MulAut.conj_apply]
        exact (Subgroup.mem_normalizer_iff.1 hxJ b).1 hb.1
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxW hb.2) (Subgroup.inv_mem _ hxW)
  exact hle ht

end Aux

variable {K : Type} [Field K]

theorem zeta_pow_ne {p : ℕ} (hp : p.Prime) {ζ : Kˣ} (hz : IsZeta p ζ) {k : ℕ}
    (hk3 : k ^ 3 % p = 1) (hk1 : k % p ≠ 1) : (ζ : K) ^ k ≠ (ζ : K) := by
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk3
      simp at hk3
    · exact h0
  intro e
  have e' : ζ ^ k = ζ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact e)
  have h3 : ζ ^ (k - 1) = 1 := by
    have : ζ ^ (k - 1) * ζ = ζ := by
      rw [← pow_succ, Nat.sub_add_cancel hk0]
      exact e'
    exact mul_eq_right.1 this
  rw [hz.pow_eq_one_iff hp] at h3
  obtain ⟨t, ht⟩ := h3
  apply hk1
  have h6 : k = p * t + 1 := by omega
  rw [h6, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.one_lt]

theorem jLemmaK2 : JLemmaK2 := by
  intro G _ _ p A c J h w hw hw3 _ y hy hy3 k hk1 hk3 hact
  obtain ⟨f, hf1, hpf, hmodel⟩ := h.model
  obtain ⟨K, hKf, hKfin, hchar, hK, ζ, hζ, ι, hmaps, honto⟩ := exists_model_of_JGood h hpf hmodel
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hz' : IsZeta p ζ := IsZeta.of_orderOf h5 hζ
  have hζ' : IsPrimitiveRoot ζ p := by
    have := IsPrimitiveRoot.orderOf ζ
    rwa [hζ] at this
  have : NeZero p := ⟨hp.ne_zero⟩
  have hkz : ¬ p ∣ k := not_dvd_of_pow_three_mod hk3
  obtain ⟨hwJ, hwW⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨hyN, hyW⟩ := Subgroup.mem_inf.1 hy
  have hwN : w ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hwJ
  have huN : w⁻¹ * y ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hwN) hyN
  have hactu : ∀ t ∈ Tof A J, (w⁻¹ * y) * t * (w⁻¹ * y)⁻¹ = t ^ k := fun t ht => by
    have h1 := hact t ht
    calc (w⁻¹ * y) * t * (w⁻¹ * y)⁻¹ = w⁻¹ * (y * t * y⁻¹) * w := by group
      _ = t ^ k := by rw [h1]; group
  have hTu : ∀ t ∈ Tof A J, (w⁻¹ * y) * t * (w⁻¹ * y)⁻¹ ∈ Tof A J := fun t ht => by
    rw [hactu t ht]
    exact Subgroup.pow_mem _ ht k
  have hTw : ∀ t ∈ Tof A J, w * t * w⁻¹ ∈ Tof A J := fun t ht => Tof_conj_mem hwN hwW ht
  have hTw' := conjAut_Tbar (Tof_le_J h) ι hmaps honto hwN hTw
  have hTu' := conjAut_Tbar (Tof_le_J h) ι hmaps honto huN hTu
  have hactu' := conjAut_action (Tof_le_J h) ι honto huN hactu
  obtain ⟨πw, εw, σw, cw, hcw, hformw⟩ := exists_hasForm hz' (conjAut ι hwN) hTw'
  obtain ⟨πu, εu, du, σu, hstd⟩ := exists_std_normalization hz' (conjAut ι huN) hTu'
  have hformu := hasForm_of_std hstd
  obtain ⟨hπu, hσu⟩ := scalar_action hp hz' (coeff_ne_zero du) hformu hkz hactu'
  subst hπu
  have hΨy : conjAut ι hyN = conjAut ι hwN * conjAut ι huN :=
    conjAut_mul_of_eq ι hwN huN (by group) hyN
  have hΨy3 : conjAut ι hyN ^ 3 = 1 := conjAut_pow_eq_one ι hyN hy3
  have hΨw3 : conjAut ι hwN ^ 3 = 1 := conjAut_pow_eq_one ι hwN hw3
  obtain ⟨hρw, -⟩ := hformw.pow_eq_one hΨw3
  have hεw : εw = false := eps_false_of_cube hρw
  subst hεw
  have hformy := hformw.comp hformu
  obtain ⟨hρy, -⟩ := hformy.pow_eq_one (by rw [← hΨy]; exact hΨy3)
  have hεu : εu = false := by
    apply eps_false_of_cube (π := πw)
    have h1 : (rho πw false ∘ rho 1 εu) = rho πw εu := by
      funext b
      rw [Function.comp_apply, rho_comp, mul_one, Bool.false_xor]
    rw [h1] at hρy
    exact hρy
  subst hεu
  have hσuζ : σu (ζ : K) = (ζ : K) ^ k := by
    rcases hσu with ⟨-, h1⟩ | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 (by decide)
  have hΨu : ∀ x : SL3 K, conjAut ι huN (QuotientGroup.mk x) =
      QuotientGroup.mk (stdHom (KFU.diagU du) σu x) := by
    intro x
    rw [hstd x]
    exact cPerm_one _
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective (ι (QuotientGroup.mk (⟨w, hwJ⟩ : ↥J)))
  have hΨw : ∀ z : PSL3 K,
      conjAut ι hwN z = QuotientGroup.mk x₀ * z * (QuotientGroup.mk x₀)⁻¹ := by
    intro z
    rw [conjAut_of_mem ι hwN hwJ z, hx₀]
  let Gm : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL x₀ * KFU.diagU du
  have hΨy' : ∀ x : SL3 K, conjAut ι hyN (QuotientGroup.mk x) =
      QuotientGroup.mk (stdHom Gm σu x) := by
    intro x
    rw [hΨy, MulAut.mul_apply, hΨu x, hΨw, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← slConj_toGL, slConj_stdHom]
  have hcube : ∀ x : SL3 K,
      (QuotientGroup.mk (stdHom (Gm * glMap σu Gm * glMap (σu * σu) Gm) (σu * σu * σu) x) :
        PSL3 K) = QuotientGroup.mk x := by
    intro x
    rw [← stdHom_cube]
    have h3 : (conjAut ι hyN ^ 3) (QuotientGroup.mk x) = QuotientGroup.mk x := by
      rw [hΨy3]
      rfl
    have h4 : (conjAut ι hyN ^ 3) (QuotientGroup.mk x) =
        conjAut ι hyN (conjAut ι hyN (conjAut ι hyN (QuotientGroup.mk x))) := by
      simp [pow_succ, MulAut.mul_apply]
    rw [h4, hΨy', hΨy', hΨy'] at h3
    exact h3
  obtain ⟨hσ3, c', hc0, hcN⟩ := std_unique hcube
  have hσu1 : σu ≠ 1 := by
    intro h1
    apply zeta_pow_ne hp hz' hk3 hk1
    rw [← hσuζ, h1]
    rfl
  have hord : orderOf σu = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [pow_three', hσ3]) hσu1
  have hcGL : Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c' hc0) =
      Gm * glMap σu Gm * glMap (σu * σu) Gm := by
    apply Units.ext
    exact hcN.symm
  obtain ⟨g, hg⟩ := exists_conj_fixed hp ⟨ζ, hζ'⟩ hord hcGL
    (fun t ht => map_eq_pow_of_mem_Tor hζ' hσuζ ht)
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥J)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.generic.center_pPrime
  have hε := KFU.isCentralPQuot_center (p := p) ι hcop
  obtain ⟨q, hq⟩ := ι.surjective (QuotientGroup.mk g⁻¹)
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hlJ : (l₀ : G) ∈ J := l₀.2
  have key : ∀ a ∈ Tof A J, y * ((l₀ : G) * a * (l₀ : G)⁻¹) * y⁻¹ =
      ((l₀ : G) * a * (l₀ : G)⁻¹) ^ k := by
    intro a ha
    obtain ⟨t', ht', hmk⟩ := mem_Tbar_iff.1 (hmaps a ha)
    let aJ : ↥J := ⟨a, Tof_le_J h ha⟩
    let a' : ↥J := l₀ * aJ * l₀⁻¹
    have haJp : aJ ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact Sec12Three.pow_eq_one_of_mem_A h.hyp (Tof_le A J ha)
    have ha'p : a' ^ p = 1 := by
      show (l₀ * aJ * l₀⁻¹) ^ p = 1
      rw [conj_pow, haJp, mul_one, mul_inv_cancel]
    have e1 : ι (QuotientGroup.mk a') = QuotientGroup.mk (g⁻¹ * t' * g) := by
      show ι (QuotientGroup.mk (l₀ * aJ * l₀⁻¹)) = _
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
        map_inv, hq, ← hmk, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        inv_inv]
    have e2 : ι (QuotientGroup.mk (jConj hyN a')) = ι (QuotientGroup.mk (a' ^ k)) := by
      rw [← conjAut_apply, e1, hΨy', hg t' ht', QuotientGroup.mk_pow, ← e1, QuotientGroup.mk_pow,
        map_pow]
    have e3 : jConj hyN a' = a' ^ k :=
      hε.eq_of_map_eq (by rw [← map_pow, ha'p, map_one])
        (by rw [← pow_mul, mul_comm, pow_mul, ha'p, one_pow]) e2
    have e4 := congrArg Subtype.val e3
    rw [jConj_apply, Subgroup.coe_pow] at e4
    exact e4
  have hfinal : ∀ a ∈ Tof A J, ((l₀ : G)⁻¹ * y * l₀) * a * ((l₀ : G)⁻¹ * y * l₀)⁻¹ = a ^ k := by
    intro a ha
    calc ((l₀ : G)⁻¹ * y * l₀) * a * ((l₀ : G)⁻¹ * y * l₀)⁻¹
        = (l₀ : G)⁻¹ * (y * ((l₀ : G) * a * (l₀ : G)⁻¹) * y⁻¹) * l₀ := by group
      _ = (l₀ : G)⁻¹ * (((l₀ : G) * a * (l₀ : G)⁻¹) ^ k) * l₀ := by rw [key a ha]
      _ = a ^ k := by rw [conj_pow]; group
  refine ⟨(l₀ : G), hlJ, ?_, hfinal⟩
  refine Subgroup.mem_normalizer_fintype (S := (Tof A J : Set G)) ?_
  intro n hn
  rw [hfinal n hn]
  exact Subgroup.pow_mem _ hn k

end CFSG.RankThree.PartOne.KFOUT3
