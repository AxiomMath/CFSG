module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

private lemma s16c11_v1_exists_unique_decomp {W' : Type} [CommGroup W'] {I₀ I₁ : Subgroup W'}
    (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤) (w : W') :
    ∃! x : ↥I₀ × ↥I₁, (x.1 : W') * x.2 = w := by
  have hdisj : Disjoint I₀ I₁ := disjoint_iff.2 hinf
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ I₀, ∃ b ∈ I₁, a * b = w := by
    have hw : w ∈ I₀ ⊔ I₁ := by rw [hsup]; exact Subgroup.mem_top w
    exact Subgroup.mem_sup.1 hw
  refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab, ?_⟩
  rintro ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h'
  exact mul_injective_of_disjoint hdisj (h'.trans hab.symm)

private lemma s16c11_v1_fst_eq_of_mul_eq {W' : Type} [CommGroup W'] {I₀ I₁ : Subgroup W'}
    (hdisj : Disjoint I₀ I₁) (a a' : ↥I₀) (b b' : ↥I₁)
    (h : (a : W') * b = (a' : W') * b') : a = a' := by
  have hx : (a, b) = (a', b') := mul_injective_of_disjoint hdisj h
  exact congrArg Prod.fst hx

private noncomputable def s16c11_v1_complement {W' : Type} [CommGroup W'] {I₀ I₁ : Subgroup W'}
    (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤) : IsComplement' I₀ I₁ :=
  (isComplement_iff_existsUnique (S := (I₀ : Set W')) (T := (I₁ : Set W'))).2
    (s16c11_v1_exists_unique_decomp hinf hsup)

private noncomputable def s16c11_v1_proj₀ {W' : Type} [CommGroup W'] {I₀ I₁ : Subgroup W'}
    (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤) : W' →* ↥I₀ where
  toFun w := ((s16c11_v1_complement hinf hsup).equiv w).1
  map_one' := by
    let hc := s16c11_v1_complement hinf hsup
    change (hc.equiv 1).1 = 1
    rw [hc.equiv_one I₀.one_mem I₁.one_mem]
    rfl
  map_mul' a b := by
    let hc := s16c11_v1_complement hinf hsup
    change (hc.equiv (a * b)).1 = (hc.equiv a).1 * (hc.equiv b).1
    have hdisj : Disjoint I₀ I₁ := disjoint_iff.2 hinf
    refine s16c11_v1_fst_eq_of_mul_eq hdisj (hc.equiv (a * b)).1
      ((hc.equiv a).1 * (hc.equiv b).1) (hc.equiv (a * b)).2
      ((hc.equiv a).2 * (hc.equiv b).2) ?_
    rw [hc.equiv_fst_mul_equiv_snd (a * b)]
    rw [show (((hc.equiv a).1 * (hc.equiv b).1 : ↥I₀) : W') *
          (((hc.equiv a).2 * (hc.equiv b).2 : ↥I₁) : W') =
        (((hc.equiv a).1 : W') * (hc.equiv b).1) *
          (((hc.equiv a).2 : W') * (hc.equiv b).2) from rfl]
    rw [mul_mul_mul_comm, hc.equiv_fst_mul_equiv_snd a, hc.equiv_fst_mul_equiv_snd b]

private lemma s16c11_v1_proj₀_eq_one_iff {W' : Type} [CommGroup W'] {I₀ I₁ : Subgroup W'}
    (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤) (w : W') :
    s16c11_v1_proj₀ hinf hsup w = 1 ↔ w ∈ I₁ := by
  let hc := s16c11_v1_complement hinf hsup
  have hfun : s16c11_v1_proj₀ hinf hsup w = (hc.equiv w).1 := rfl
  have hdisj : Disjoint I₀ I₁ := disjoint_iff.2 hinf
  constructor
  · intro h
    have h1 : (hc.equiv w).1 = 1 := hfun ▸ h
    have hw2 : w = ((hc.equiv w).2 : W') := by
      calc w = ((hc.equiv w).1 : W') * ((hc.equiv w).2 : W') :=
            (hc.equiv_fst_mul_equiv_snd w).symm
        _ = ((hc.equiv w).2 : W') := by rw [h1]; simp
    rw [hw2]
    exact (hc.equiv w).2.2
  · intro hw
    have hpair : (hc.equiv w).1 = 1 := by
      refine s16c11_v1_fst_eq_of_mul_eq hdisj (hc.equiv w).1 1 (hc.equiv w).2
        ⟨w, hw⟩ ?_
      calc ((hc.equiv w).1 : W') * ((hc.equiv w).2 : W')
          = w := hc.equiv_fst_mul_equiv_snd w
        _ = ((1 : ↥I₀) : W') * ((⟨w, hw⟩ : ↥I₁) : W') := by simp
    rw [hfun]
    exact hpair

private lemma s16c11_v1_proj₀_mulAut {W' : Type} [CommGroup W'] {B : Subgroup (MulAut W')}
    {I₀ I₁ : Subgroup W'} (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤)
    (hI₀ : StableUnder B I₀) (hI₁ : StableUnder B I₁)
    (b : MulAut W') (hb : b ∈ B) (w : W') :
    ((s16c11_v1_proj₀ hinf hsup (b w) : ↥I₀) : W') =
      b ((s16c11_v1_proj₀ hinf hsup w : ↥I₀) : W') := by
  let hc := s16c11_v1_complement hinf hsup
  have hfun : ∀ w, s16c11_v1_proj₀ hinf hsup w = (hc.equiv w).1 := fun w => rfl
  have hdisj : Disjoint I₀ I₁ := disjoint_iff.2 hinf
  have hpair : (hc.equiv (b w)).1 =
      ⟨b ((hc.equiv w).1 : W'), hI₀ b hb ((hc.equiv w).1 : W') (hc.equiv w).1.2⟩ := by
    refine s16c11_v1_fst_eq_of_mul_eq hdisj (hc.equiv (b w)).1
      ⟨b ((hc.equiv w).1 : W'), hI₀ b hb ((hc.equiv w).1 : W') (hc.equiv w).1.2⟩
      (hc.equiv (b w)).2
      ⟨b ((hc.equiv w).2 : W'), hI₁ b hb ((hc.equiv w).2 : W') (hc.equiv w).2.2⟩ ?_
    rw [hc.equiv_fst_mul_equiv_snd (b w), ← map_mul, hc.equiv_fst_mul_equiv_snd w]
  simpa [hfun] using congrArg Subtype.val hpair

theorem s16c11_v1_exists_iso_summand {W' : Type} [CommGroup W'] {B : Subgroup (MulAut W')}
    {I₀ I₁ N N' : Subgroup W'} (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤)
    (hirr₀ : IsIrrOn B I₀ ⊥) (hirr₁ : IsIrrOn B I₁ ⊥) (hN : StableUnder B N)
    (hN' : StableUnder B N') (hNinf : N ⊓ N' = ⊥) (hNsup : N ⊔ N' = ⊤) (hN0 : N ≠ ⊥)
    (hN'0 : N' ≠ ⊥) :
    ∃ (I : Subgroup W') (s : ↥N →* ↥I), (I = I₀ ∨ I = I₁) ∧ Function.Bijective s ∧
      ∀ (b : MulAut W') (hb : b ∈ B) (n : ↥N),
        ((s ⟨b (n : W'), hN b hb (n : W') n.2⟩ : ↥I) : W') = b ((s n : ↥I) : W') := by
  have hI₀ : StableUnder B I₀ := hirr₀.2.1
  have hI₁ : StableUnder B I₁ := hirr₁.2.1
  have hstabN₀ : StableUnder B (N ⊓ I₀) := fun b hb x hx =>
    ⟨hN b hb x hx.1, hI₀ b hb x hx.2⟩
  have hstabN₁ : StableUnder B (N ⊓ I₁) := fun b hb x hx =>
    ⟨hN b hb x hx.1, hI₁ b hb x hx.2⟩
  have hN₀ : N ⊓ I₀ = ⊥ ∨ N ⊓ I₀ = I₀ :=
    hirr₀.2.2.2 (N ⊓ I₀) hstabN₀ bot_le inf_le_right
  have hN₁ : N ⊓ I₁ = ⊥ ∨ N ⊓ I₁ = I₁ :=
    hirr₁.2.2.2 (N ⊓ I₁) hstabN₁ bot_le inf_le_right
  by_cases hI0N : I₀ ≤ N
  · have hnotI1 : ¬ I₁ ≤ N := by
      intro hI1N
      have htop : N = ⊤ := by
        rw [eq_top_iff, ← hsup]
        exact sup_le hI0N hI1N
      have hN'bot : N' = ⊥ := by
        have h : N' ⊓ N = ⊥ := by rw [inf_comm]; exact hNinf
        simpa [htop] using h
      exact hN'0 hN'bot
    have hNinf₁ : N ⊓ I₁ = ⊥ := by
      rcases hN₁ with h | h
      · exact h
      · exact absurd (h ▸ inf_le_left) hnotI1
    have hNle₀ : N ≤ I₀ := by
      intro n hn
      have hn' : n ∈ I₀ ⊔ I₁ := by rw [hsup]; exact Subgroup.mem_top n
      rw [Subgroup.mem_sup] at hn'
      obtain ⟨i₀, hi₀, i₁, hi₁, hi⟩ := hn'
      have hi₁N : i₁ ∈ N := by
        have : i₁ = i₀⁻¹ * n := by rw [← hi]; group
        rw [this]
        exact N.mul_mem (N.inv_mem (hI0N hi₀)) hn
      have : i₁ ∈ N ⊓ I₁ := ⟨hi₁N, hi₁⟩
      rw [hNinf₁] at this
      have hi₁one : i₁ = 1 := Subgroup.mem_bot.1 this
      rw [← hi, hi₁one, mul_one]
      exact hi₀
    refine ⟨I₀, Subgroup.inclusion hNle₀, Or.inl rfl, ?_, ?_⟩
    · exact ⟨Subgroup.inclusion_injective hNle₀, fun y =>
        ⟨⟨(y : W'), hI0N y.2⟩, Subtype.ext rfl⟩⟩
    · intro b hb n
      simp only [Subgroup.coe_inclusion]
  · by_cases hI1N : I₁ ≤ N
    · have hNinf₀ : N ⊓ I₀ = ⊥ := by
        rcases hN₀ with h | h
        · exact h
        · exact absurd (h ▸ inf_le_left) hI0N
      have hNle₁ : N ≤ I₁ := by
        intro n hn
        have hn' : n ∈ I₀ ⊔ I₁ := by rw [hsup]; exact Subgroup.mem_top n
        rw [Subgroup.mem_sup] at hn'
        obtain ⟨i₀, hi₀, i₁, hi₁, hi⟩ := hn'
        have hi₀N : i₀ ∈ N := by
          have : i₀ = n * i₁⁻¹ := by rw [← hi]; group
          rw [this]
          exact N.mul_mem hn (N.inv_mem (hI1N hi₁))
        have : i₀ ∈ N ⊓ I₀ := ⟨hi₀N, hi₀⟩
        rw [hNinf₀] at this
        have hi₀one : i₀ = 1 := Subgroup.mem_bot.1 this
        rw [← hi, hi₀one, one_mul]
        exact hi₁
      refine ⟨I₁, Subgroup.inclusion hNle₁, Or.inr rfl, ?_, ?_⟩
      · exact ⟨Subgroup.inclusion_injective hNle₁, fun y =>
          ⟨⟨(y : W'), hI1N y.2⟩, Subtype.ext rfl⟩⟩
      · intro b hb n
        simp only [Subgroup.coe_inclusion]
    · have hNinf₀ : N ⊓ I₀ = ⊥ := by
        rcases hN₀ with h | h
        · exact h
        · exact absurd (h ▸ inf_le_left) hI0N
      have hNinf₁ : N ⊓ I₁ = ⊥ := by
        rcases hN₁ with h | h
        · exact h
        · exact absurd (h ▸ inf_le_left) hI1N
      let p₀ := s16c11_v1_proj₀ hinf hsup
      have hp₀_equiv : ∀ (b : MulAut W') (hb : b ∈ B) (w : W'),
          ((p₀ (b w) : ↥I₀) : W') = b ((p₀ w : ↥I₀) : W') :=
        fun b hb w => s16c11_v1_proj₀_mulAut hinf hsup hI₀ hI₁ b hb w
      have hp₀_ker : ∀ w : W', p₀ w = 1 ↔ w ∈ I₁ :=
        fun w => s16c11_v1_proj₀_eq_one_iff hinf hsup w
      let s : ↥N →* ↥I₀ := p₀.comp N.subtype
      refine ⟨I₀, s, Or.inl rfl, ?_, ?_⟩
      · constructor
        · intro x y hxy
          have hxy' : p₀ (x : W') = p₀ (y : W') := hxy
          have hxy'' : p₀ ((x : W') * (y : W')⁻¹) = 1 := by
            rw [map_mul, map_inv, hxy', mul_inv_cancel]
          have hmemI₁ : (x : W') * (y : W')⁻¹ ∈ I₁ := (hp₀_ker _).1 hxy''
          have hmemN : (x : W') * (y : W')⁻¹ ∈ N := N.mul_mem x.2 (N.inv_mem y.2)
          have : (x : W') * (y : W')⁻¹ ∈ N ⊓ I₁ := ⟨hmemN, hmemI₁⟩
          rw [hNinf₁] at this
          exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 this))
        · intro y
          let J : Subgroup W' := N.map (I₀.subtype.comp p₀)
          have hJle : J ≤ I₀ := by
            intro z hz
            rcases Subgroup.mem_map.1 hz with ⟨n, hn, rfl⟩
            exact (p₀ n).2
          have hJstab : StableUnder B J := by
            intro b hb z hz
            rcases Subgroup.mem_map.1 hz with ⟨n, hn, rfl⟩
            exact Subgroup.mem_map.2 ⟨b n, hN b hb n hn, hp₀_equiv b hb (n : W')⟩
          have hJne : J ≠ ⊥ := by
            intro hJbot
            apply hN0
            refine le_bot_iff.1 fun n hn => ?_
            have hp1 : p₀ n = 1 := by
              have : (p₀ n : W') ∈ J := Subgroup.mem_map.2 ⟨n, hn, rfl⟩
              rw [hJbot] at this
              exact Subtype.ext (Subgroup.mem_bot.1 this)
            have hnI₁ : n ∈ I₁ := (hp₀_ker n).1 hp1
            have : n ∈ N ⊓ I₁ := ⟨hn, hnI₁⟩
            rw [hNinf₁] at this
            exact Subgroup.mem_bot.1 this
          have hJtop : J = I₀ := by
            rcases hirr₀.2.2.2 J hJstab bot_le hJle with h | h
            · exact absurd h hJne
            · exact h
          have hy : (y : W') ∈ J := by rw [hJtop]; exact y.2
          rcases Subgroup.mem_map.1 hy with ⟨n, hn, hny⟩
          exact ⟨⟨n, hn⟩, Subtype.ext hny⟩
      · intro b hb n
        exact hp₀_equiv b hb (n : W')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
