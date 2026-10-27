module

public import CFSG.Quasithin.H13.NQCatA314L35Par

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix CFSG.Quasithin

theorem isMaxParabolicOf_map {X Y : Type} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    (hf : Function.Injective f) {P : Subgroup X} (h : IsMaxParabolicOf p ⊤ P) :
    IsMaxParabolicOf p f.range (P.map f) := by
  obtain ⟨⟨-, S, hS, hN⟩, hne, hmax⟩ := h
  have hsyl : ∀ H : Subgroup X, IsSylowOf p H ⊤ → IsSylowOf p (H.map f) f.range := by
    rintro H ⟨-, hH2, hHi⟩
    refine ⟨Subgroup.map_le_range f H, hH2.map f, ?_⟩
    have e : ((H.map f).subgroupOf f.range).index = (H.subgroupOf ⊤).index := by
      show (H.map f).relIndex f.range = H.relIndex ⊤
      rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective H ⊤ hf]
    rw [e]
    exact hHi
  have hsyl' : ∀ H : Subgroup Y, IsSylowOf p H f.range → IsSylowOf p (H.comap f) ⊤ := by
    rintro H ⟨-, hH2, hHi⟩
    refine ⟨le_top, hH2.comap_of_injective f hf, ?_⟩
    have e : ((H.comap f).subgroupOf ⊤).index = (H.subgroupOf f.range).index := by
      rw [show ((H.comap f).subgroupOf ⊤).index = (H.comap f).index from
        Subgroup.relIndex_top_right _, Subgroup.index_comap]
      rfl
    rw [e]
    exact hHi
  have hnorm : ∀ H : Subgroup X,
      f.range ⊓ Subgroup.normalizer ((H.map f : Subgroup Y) : Set Y) ≤
        (⊤ ⊓ Subgroup.normalizer (H : Set X)).map f := by
    intro H y hy0
    obtain ⟨hyR, hy⟩ := Subgroup.mem_inf.mp hy0
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hyR
    refine ⟨x, ⟨trivial, ?_⟩, rfl⟩
    show x ∈ Subgroup.normalizer (H : Set X)
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro k
    have h1 := hy (f k)
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hf,
      Subgroup.mem_map_iff_mem hf] at h1
    exact h1
  refine ⟨⟨Subgroup.map_le_range f P, S.map f, hsyl S hS, (hnorm S).trans (Subgroup.map_mono hN)⟩,
    ?_, ?_⟩
  · intro h1
    apply hne
    exact eq_top_iff.mpr fun x _ => (Subgroup.mem_map_iff_mem hf).mp (h1 ▸ ⟨x, rfl⟩)
  · rintro Q ⟨hQR, S₁, hS₁, hS₁N⟩ hQne hPQ
    have hQ0 : Q.comap f ≠ ⊤ := by
      intro h1
      apply hQne
      apply le_antisymm hQR
      rintro _ ⟨x, rfl⟩
      have : x ∈ Q.comap f := h1 ▸ Subgroup.mem_top x
      exact this
    have hPQ0 : P ≤ Q.comap f := fun x hx => hPQ ⟨x, hx, rfl⟩
    have hN0 : ⊤ ⊓ Subgroup.normalizer ((S₁.comap f : Subgroup X) : Set X) ≤ Q.comap f := by
      rintro x ⟨-, hx⟩
      have hS₁eq : (S₁.comap f).map f = S₁ := Subgroup.map_comap_eq_self hS₁.1
      have h1 : f x ∈ Subgroup.normalizer (((S₁.comap f).map f : Subgroup Y) : Set Y) :=
        Subgroup.le_normalizer_map f ⟨x, hx, rfl⟩
      rw [hS₁eq] at h1
      exact hS₁N ⟨⟨x, rfl⟩, h1⟩
    have h1 := hmax (Q.comap f) ⟨le_top, S₁.comap f, hsyl' S₁ hS₁, hN0⟩ hQ0 hPQ0
    rw [← h1, Subgroup.map_comap_eq_self hQR]

theorem z0_eq_comm :
    uMk (1, 0, 0) * uMk (0, 0, 1) = uMk (0, 1, 0) * (uMk (0, 0, 1) * uMk (1, 0, 0)) := by
  ext i j
  show ((uMk (1, 0, 0) : Matrix (Fin 3) (Fin 3) (ZMod 5)) *
      (uMk (0, 0, 1) : Matrix (Fin 3) (Fin 3) (ZMod 5))) i j =
    ((uMk (0, 1, 0) : Matrix (Fin 3) (Fin 3) (ZMod 5)) *
      ((uMk (0, 0, 1) : Matrix (Fin 3) (Fin 3) (ZMod 5)) *
        (uMk (1, 0, 0) : Matrix (Fin 3) (Fin 3) (ZMod 5)))) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, uMk]

theorem z0_mem {V : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5))} (hVU : V ≤ U5)
    (hV : Nat.card V = 25) : uMk (0, 1, 0) ∈ V := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set V' := V.subgroupOf U5 with hV'
  have hV'c : Nat.card V' = 25 := by
    rw [hV', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv, hV]
  have hidx : V'.index = 5 := by
    have h := V'.index_mul_card
    rw [hV'c, card_U5] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 25) (h.trans (by norm_num))
  have hmin : (Nat.card ↥U5).minFac = 5 := by
    rw [card_U5]
    norm_num
  have hnorm : V'.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
  have hQ : Nat.card (↥U5 ⧸ V') = 5 := by rw [← Subgroup.index_eq_card, hidx]
  have : Fact (Nat.card (↥U5 ⧸ V')).Prime := ⟨by rw [hQ]; norm_num⟩
  have hcyc : IsCyclic (↥U5 ⧸ V') := isCyclic_of_prime_card rfl
  set x : ↥U5 := ⟨uMk (1, 0, 0), uMk_mem _⟩
  set y : ↥U5 := ⟨uMk (0, 0, 1), uMk_mem _⟩
  set z : ↥U5 := ⟨uMk (0, 1, 0), uMk_mem _⟩
  have hxy : x * y = z * (y * x) := Subtype.ext z0_eq_comm
  have hcomm : ∀ a b : ↥U5 ⧸ V', a * b = b * a := fun a b => IsCyclic.commGroup.mul_comm a b
  have h1 : (QuotientGroup.mk z : ↥U5 ⧸ V') = 1 := by
    have h2 : (QuotientGroup.mk x : ↥U5 ⧸ V') * QuotientGroup.mk y =
        QuotientGroup.mk z * (QuotientGroup.mk y * QuotientGroup.mk x) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
    rw [hcomm (QuotientGroup.mk y)] at h2
    exact mul_eq_right.mp h2.symm
  have h4 : z ∈ V' := (QuotientGroup.eq_one_iff z).mp h1
  exact Subgroup.mem_subgroupOf.mp h4

theorem exists_maxParabolic_sl35 {B V : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5))}
    (hBV : B ≤ Subgroup.normalizer (V : Set (SpecialLinearGroup (Fin 3) (ZMod 5))))
    (hV : Nat.card V = 25) :
    ∃ P : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5)), IsMaxParabolicOf 5 ⊤ P ∧ B ≤ P ∧
      Nat.card ↥⁅P, P⁆ ≤ 3000 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hV5 : IsPGroup 5 V := IsPGroup.of_card (n := 2) (by rw [hV]; norm_num)
  obtain ⟨S, hVS⟩ := hV5.exists_le_sylow
  have hUi : ¬ 5 ∣ U5.index := by
    have h := isSylowOf_U5.2.2
    rwa [show (U5.subgroupOf ⊤).index = U5.index from Subgroup.relIndex_top_right _] at h
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) (ZMod 5))
    (isSylowOf_U5.2.1.toSylow hUi) S
  have hS : (S : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5))) =
      U5.map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  set α : MulAut (SpecialLinearGroup (Fin 3) (ZMod 5)) := MulAut.conj c with hα
  set V' := V.map α.symm.toMonoidHom with hV'
  set B' := B.map α.symm.toMonoidHom with hB'
  have hVU : V' ≤ U5 := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 : v ∈ U5.map α.toMonoidHom := hS ▸ hVS hv
    obtain ⟨u, hu, rfl⟩ := h1
    simpa using hu
  have hV'c : Nat.card V' = 25 := by
    rw [hV', Subgroup.card_map_of_injective α.symm.injective, hV]
  have hB'V : B' ≤ Subgroup.normalizer (V' : Set (SpecialLinearGroup (Fin 3) (ZMod 5))) := by
    rw [hB', hV']
    exact (Subgroup.map_mono hBV).trans (Subgroup.le_normalizer_map _)
  have hz := z0_mem hVU hV'c
  have hconj : ∀ b ∈ B', ∀ v ∈ V', b⁻¹ * v * b ∈ V' := by
    intro b hb v hv
    have h1 := (Subgroup.mem_normalizer_iff.mp (hB'V (B'.inv_mem hb)) v).mp hv
    simpa using h1
  have key : ∀ b ∈ B', ∀ v ∈ V', ∀ j : Fin 3,
      ((v * b : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 j =
        ((b * (b⁻¹ * v * b) : SpecialLinearGroup (Fin 3) (ZMod 5)) :
          Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 j := by
    intro b _ v _ j
    rw [show b * (b⁻¹ * v * b) = v * b by group]
  have h20 : ∀ b ∈ B', (b : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 0 = 0 := by
    intro b hb
    have h1 := key b hb _ hz 0
    obtain ⟨w1, w2, -, w4, -, -⟩ := hVU (hconj b hb _ hz)
    rw [sl35_mul_apply, sl35_mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, w1, w2, w4] at h1
    simp [uMk] at h1
    exact h1
  by_cases hfix : ∀ v ∈ V', (v : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 1 = 0
  ·
    have hle : B' ≤ Ppl := by
      intro b hb
      refine ⟨h20 b hb, ?_⟩
      have h1 := key b hb _ hz 1
      have hw := hconj b hb _ hz
      obtain ⟨-, -, w3, -, w5, -⟩ := hVU hw
      have w0 := hfix _ hw
      rw [sl35_mul_apply, sl35_mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, w0, w3,
        w5] at h1
      simp [uMk] at h1
      exact h1
    refine ⟨Ppl.map α.toMonoidHom, ?_, ?_, ?_⟩
    · have h1 := isMaxParabolicOf_map α.toMonoidHom α.injective isMaxParabolicOf_Ppl
      rwa [MonoidHom.range_eq_top_of_surjective _ α.surjective] at h1
    · intro b hb
      refine ⟨α.symm b, hle ⟨b, hb, rfl⟩, ?_⟩
      simp
    · calc Nat.card ↥⁅Ppl.map α.toMonoidHom, Ppl.map α.toMonoidHom⁆
          = Nat.card ↥(⁅Ppl, Ppl⁆.map α.toMonoidHom) := by rw [Subgroup.map_commutator]
        _ = Nat.card ↥⁅Ppl, Ppl⁆ := Subgroup.card_map_of_injective α.injective
        _ ≤ Nat.card Kpl := Subgroup.card_le_of_le commutator_Ppl_le
        _ = 3000 := card_Kpl
  ·
    push Not at hfix
    obtain ⟨x₀, hx₀, ha⟩ := hfix
    have hle : B' ≤ Pl := by
      intro b hb
      refine ⟨?_, h20 b hb⟩
      have h1 := key b hb _ hx₀ 0
      obtain ⟨w1, w2, -, w4, -, -⟩ := hVU (hconj b hb _ hx₀)
      obtain ⟨-, -, -, x4, -, -⟩ := hVU hx₀
      rw [sl35_mul_apply, sl35_mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, w1, w2, w4,
        x4, h20 b hb] at h1
      have h2 : (x₀ : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 1 *
          (b : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 0 = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_left ha
    refine ⟨Pl.map α.toMonoidHom, ?_, ?_, ?_⟩
    · have h1 := isMaxParabolicOf_map α.toMonoidHom α.injective isMaxParabolicOf_Pl
      rwa [MonoidHom.range_eq_top_of_surjective _ α.surjective] at h1
    · intro b hb
      refine ⟨α.symm b, hle ⟨b, hb, rfl⟩, ?_⟩
      simp
    · calc Nat.card ↥⁅Pl.map α.toMonoidHom, Pl.map α.toMonoidHom⁆
          = Nat.card ↥(⁅Pl, Pl⁆.map α.toMonoidHom) := by rw [Subgroup.map_commutator]
        _ = Nat.card ↥⁅Pl, Pl⁆ := Subgroup.card_map_of_injective α.injective
        _ ≤ Nat.card Kl := Subgroup.card_le_of_le commutator_Pl_le
        _ = 3000 := card_Kl

end CFSG.Quasithin.H13.NQCat.A314D
