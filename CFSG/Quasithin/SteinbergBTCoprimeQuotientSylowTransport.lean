module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup

theorem coprime_abelian_quotient_Sylow_action_transport {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (A X : Subgroup L) [A.Normal] [X.Normal] (hAX : A ≤ X)
    (hA : ¬p ∣ Nat.card A) {d : ℕ}
    (hXe : CFSG.IsElementaryAbelian p (X.map (QuotientGroup.mk' A)))
    (hXcard : Nat.card (X.map (QuotientGroup.mk' A)) = p ^ d) (P : Subgroup L)
    (hP : ∃ S : Sylow p X, (S : Subgroup X).map X.subtype = P) :
    (P ⊓ A = ⊥ ∧ P.map (QuotientGroup.mk' A) = X.map (QuotientGroup.mk' A)) ∧
    (∀ g : L, ∃ x ∈ X, ∃ n ∈ normalizer (P : Set L), g = x * n) ∧
    (∀ g : L, ∃ n ∈ normalizer (P : Set L), ∀ y ∈ X.map (QuotientGroup.mk' A),
      (g : L ⧸ A) * y * (g : L ⧸ A)⁻¹ = (n : L ⧸ A) * y * (n : L ⧸ A)⁻¹) ∧
    (∀ n ∈ normalizer (P : Set L), ∀ u ∈ P, n * u * n⁻¹ ∈ P ∧
      ((n * u * n⁻¹ : L) : L ⧸ A) = (n : L ⧸ A) * (u : L ⧸ A) * (n : L ⧸ A)⁻¹) ∧
    (Group.IsPerfect L →
      (∀ W : Subgroup (L ⧸ A), W ≤ X.map (QuotientGroup.mk' A) →
        (∀ g : L, ∀ w ∈ W, (g : L ⧸ A) * w * (g : L ⧸ A)⁻¹ ∈ W) →
        W = ⊥ ∨ W = X.map (QuotientGroup.mk' A)) →
      ¬∃ T : Finset (Subgroup L), T.Nonempty ∧ T.card ≤ 2 ∧
        (∀ Q ∈ T, Q ≤ P ∧ Q ≠ ⊥ ∧ Q ≠ P) ∧
        ∀ n ∈ normalizer (P : Set L), ∀ Q ∈ T, Q.map (MulAut.conj n).toMonoidHom ∈ T) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hP
  set π := QuotientGroup.mk' A with hπ
  set Xbar := X.map π with hXbar
  have hPX : P ≤ X := by
    rw [← hS]
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  set f : X →* L ⧸ A := π.comp X.subtype with hf
  have hfker : f.ker = A.subgroupOf X := by
    ext x
    change π (x : L) = 1 ↔ (x : L) ∈ A
    exact QuotientGroup.eq_one_iff (x : L)
  have hfrange : f.range = Xbar := by rw [hf, MonoidHom.range_comp, range_subtype]
  have hXcard' : Nat.card X = Nat.card A * p ^ d := by
    rw [← card_mul_index f.ker, index_ker, hfrange, hfker,
      Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv, hXcard]
  have hPcard : Nat.card P = p ^ d := by
    have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
    rw [← hS, card_map_of_injective X.subtype_injective, S.card_eq_multiplicity, hXcard',
      Nat.factorization_mul hA0 (pow_pos hp.pos d).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hA, hp.factorization_pow, Finsupp.single_eq_same,
      zero_add]
  have hPA : P ⊓ A = ⊥ := disjoint_iff.1 (disjoint_of_coprime_natCard (by
    rw [hPcard]
    exact Nat.Coprime.pow_left d ((Nat.Prime.coprime_iff_not_dvd hp).2 hA)))
  have hinjP : ∀ u ∈ P, ∀ v ∈ P, π u = π v → u = v := by
    intro u hu v hv h
    have h1 : u⁻¹ * v ∈ A := QuotientGroup.eq.1 h
    have h2 : u⁻¹ * v ∈ P ⊓ A := mem_inf.2 ⟨mul_mem (inv_mem hu) hv, h1⟩
    rw [hPA, mem_bot] at h2
    exact (inv_mul_eq_one.1 h2)
  have hPmap : P.map π = Xbar := by
    refine eq_of_le_of_card_ge (map_mono hPX) ?_
    set g : P →* L ⧸ A := π.comp P.subtype with hg
    have hgker : g.ker = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      exact Subtype.ext (hinjP u u.2 1 P.one_mem (by rw [map_one]; exact hu))
    have hgrange : g.range = P.map π := by rw [hg, MonoidHom.range_comp, range_subtype]
    have h1 := card_mul_index g.ker
    rw [index_ker, hgker, card_bot, one_mul, hgrange, hPcard] at h1
    rw [h1, hXcard]
  have hFr : ∀ g : L, ∃ x ∈ X, ∃ n ∈ normalizer (P : Set L), g = x * n := by
    intro g
    have h := Sylow.normalizer_sup_eq_top S
    rw [hS] at h
    have hg : g ∈ (X ⊔ normalizer (P : Set L) : Subgroup L) := by
      rw [sup_comm, h]
      exact mem_top g
    rw [← SetLike.mem_coe, normal_mul] at hg
    obtain ⟨x, hx, n, hn, rfl⟩ := hg
    exact ⟨x, hx, n, hn, rfl⟩
  have hXbarN : Xbar.Normal := (inferInstance : X.Normal).map π (QuotientGroup.mk'_surjective A)
  have hXbarcomm : ∀ a ∈ Xbar, ∀ b ∈ Xbar, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hXe.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hconj : ∀ g : L, ∃ n ∈ normalizer (P : Set L), ∀ y ∈ Xbar,
      (g : L ⧸ A) * y * (g : L ⧸ A)⁻¹ = (n : L ⧸ A) * y * (n : L ⧸ A)⁻¹ := by
    intro g
    obtain ⟨x, hx, n, hn, rfl⟩ := hFr g
    refine ⟨n, hn, fun y hy => ?_⟩
    have hxbar : (x : L ⧸ A) ∈ Xbar := ⟨x, hx, rfl⟩
    have hny : (n : L ⧸ A) * y * (n : L ⧸ A)⁻¹ ∈ Xbar := hXbarN.conj_mem y hy _
    calc ((x * n : L) : L ⧸ A) * y * ((x * n : L) : L ⧸ A)⁻¹
        = (x : L ⧸ A) * ((n : L ⧸ A) * y * (n : L ⧸ A)⁻¹) * (x : L ⧸ A)⁻¹ := by
          rw [QuotientGroup.mk_mul]
          group
      _ = ((n : L ⧸ A) * y * (n : L ⧸ A)⁻¹) * ((x : L ⧸ A) * (x : L ⧸ A)⁻¹) := by
          rw [hXbarcomm _ hxbar _ hny]
          group
      _ = (n : L ⧸ A) * y * (n : L ⧸ A)⁻¹ := by rw [mul_inv_cancel, mul_one]
  have hint : ∀ n ∈ normalizer (P : Set L), ∀ u ∈ P, n * u * n⁻¹ ∈ P ∧
      ((n * u * n⁻¹ : L) : L ⧸ A) = (n : L ⧸ A) * (u : L ⧸ A) * (n : L ⧸ A)⁻¹ :=
    fun n hn u hu => ⟨(mem_normalizer_iff.1 hn u).1 hu, by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  refine ⟨⟨hPA, hPmap⟩, hFr, hconj, hint, fun hperf hirr => ?_⟩
  rintro ⟨T, hTne, hT2, hTsub, hTinv⟩
  have hmap_bot : ∀ Q ≤ P, Q.map π = ⊥ → Q = ⊥ := by
    intro Q hQ h
    rw [eq_bot_iff]
    intro u hu
    have h1 : π u = π 1 := by
      rw [map_one]
      have : π u ∈ Q.map π := ⟨u, hu, rfl⟩
      rwa [h, mem_bot] at this
    rw [hinjP u (hQ hu) 1 P.one_mem h1]
    exact one_mem _
  have hmap_top : ∀ Q ≤ P, Q.map π = P.map π → Q = P := by
    intro Q hQ h
    refine le_antisymm hQ fun u hu => ?_
    have : π u ∈ Q.map π := by
      rw [h]
      exact ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hvu⟩ := this
    rw [← hinjP v (hQ hv) u hu hvu]
    exact hv
  have hmap_inj : ∀ Q₁ ≤ P, ∀ Q₂ ≤ P, Q₁.map π = Q₂.map π → Q₁ = Q₂ := by
    intro Q₁ hQ₁ Q₂ hQ₂ h
    refine le_antisymm (fun u hu => ?_) (fun u hu => ?_)
    · obtain ⟨v, hv, hvu⟩ : π u ∈ Q₂.map π := h ▸ ⟨u, hu, rfl⟩
      rw [← hinjP v (hQ₂ hv) u (hQ₁ hu) hvu]
      exact hv
    · obtain ⟨v, hv, hvu⟩ : π u ∈ Q₁.map π := h.symm ▸ ⟨u, hu, rfl⟩
      rw [← hinjP v (hQ₁ hv) u (hQ₂ hu) hvu]
      exact hv
  set Φ : L → Subgroup (L ⧸ A) → Subgroup (L ⧸ A) :=
    fun g W => W.map (MulAut.conj (π g)).toMonoidHom with hΦ
  have hΦmul : ∀ g h W, Φ (g * h) W = Φ g (Φ h W) := by
    intro g h W
    simp only [hΦ, map_map]
    congr 1
    ext w
    simp [MulAut.conj_apply, mul_assoc]
  have hΦinj : ∀ g W W', Φ g W = Φ g W' → W = W' := fun g W W' h =>
    map_injective (f := (MulAut.conj (π g)).toMonoidHom) (MulAut.conj (π g)).injective h
  have hΦone : ∀ W, Φ 1 W = W := by
    intro W
    simp only [hΦ, map_one]
    ext w
    simp
  have hΦT : ∀ g, ∀ Q ∈ T, ∃ Q' ∈ T, Φ g (Q.map π) = Q'.map π := by
    intro g Q hQ
    obtain ⟨n, hn, hgn⟩ := hconj g
    have hgn' : ∀ y ∈ Xbar, π g * y * (π g)⁻¹ = π n * y * (π n)⁻¹ := hgn
    refine ⟨Q.map (MulAut.conj n).toMonoidHom, hTinv n hn Q hQ, ?_⟩
    simp only [hΦ, map_map]
    ext w
    simp only [mem_map, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q, hq, ?_⟩
      rw [hgn' _ ⟨q, hPX ((hTsub Q hQ).1 hq), rfl⟩, map_mul, map_mul, map_inv]
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q, hq, ?_⟩
      rw [hgn' _ ⟨q, hPX ((hTsub Q hQ).1 hq), rfl⟩, map_mul, map_mul, map_inv]
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hT⟩ : ∃ Q₁ ∈ T, ∃ Q₂ ∈ T, ∀ Q ∈ T, Q = Q₁ ∨ Q = Q₂ := by
    have hpos := Finset.card_pos.2 hTne
    rcases (show T.card = 1 ∨ T.card = 2 by omega) with h1 | h2
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
      exact ⟨a, Finset.mem_singleton_self a, a, Finset.mem_singleton_self a,
        fun Q hQ => Or.inl (Finset.mem_singleton.1 hQ)⟩
    · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.1 h2
      refine ⟨a, Finset.mem_insert_self a _, b, Finset.mem_insert_of_mem
        (Finset.mem_singleton_self b), fun Q hQ => ?_⟩
      rcases Finset.mem_insert.1 hQ with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.1 h)
  set W₁ := Q₁.map π with hW₁
  set W₂ := Q₂.map π with hW₂
  have hperm : ∀ g, ∀ W, (W = W₁ ∨ W = W₂) → (Φ g W = W₁ ∨ Φ g W = W₂) := by
    rintro g W (rfl | rfl)
    · obtain ⟨Q', hQ', h⟩ := hΦT g Q₁ hQ₁
      rcases hT Q' hQ' with rfl | rfl
      · exact Or.inl h
      · exact Or.inr h
    · obtain ⟨Q', hQ', h⟩ := hΦT g Q₂ hQ₂
      rcases hT Q' hQ' with rfl | rfl
      · exact Or.inl h
      · exact Or.inr h
  have hfix : ∀ g, Φ g W₁ = W₁ := by
    by_cases hW : W₁ = W₂
    · intro g
      rcases hperm g W₁ (Or.inl rfl) with h | h
      · exact h
      · rw [h, hW]
    ·
      have hswap : ∀ g, Φ g W₁ ≠ W₁ → Φ g W₂ = W₁ := by
        intro g hg
        rcases hperm g W₂ (Or.inr rfl) with h | h
        · exact h
        · have h1 : Φ g W₁ = W₂ := (hperm g W₁ (Or.inl rfl)).resolve_left hg
          exact absurd (hΦinj g _ _ (h1.trans h.symm)) hW
      have hkeep : ∀ g, Φ g W₁ = W₁ → Φ g W₂ = W₂ := by
        intro g hg
        rcases hperm g W₂ (Or.inr rfl) with h | h
        · exact absurd (hΦinj g _ _ (hg.trans h.symm)) hW
        · exact h
      have hiff : ∀ g h, (Φ (g * h) W₁ = W₁ ↔ (Φ g W₁ = W₁ ↔ Φ h W₁ = W₁)) := by
        intro g h
        rw [hΦmul]
        by_cases hh : Φ h W₁ = W₁
        · rw [hh]
          simp
        · have h2 : Φ h W₁ = W₂ := (hperm h W₁ (Or.inl rfl)).resolve_left hh
          rw [h2]
          by_cases hg : Φ g W₁ = W₁
          · rw [hkeep g hg]
            simp [hg]
          · rw [hswap g hg]
            simp [hg, Ne.symm hW]
      let χ : L →* Multiplicative (ZMod 2) :=
        { toFun := fun g => if Φ g W₁ = W₁ then 1 else Multiplicative.ofAdd 1
          map_one' := by simp [hΦone]
          map_mul' := fun g h => by
            by_cases hg : Φ g W₁ = W₁ <;> by_cases hh : Φ h W₁ = W₁
            · simp [(hiff g h).2 (iff_of_true hg hh), hg, hh]
            · simp [show ¬Φ (g * h) W₁ = W₁ from fun h' => hh (((hiff g h).1 h').1 hg), hg, hh]
            · simp [show ¬Φ (g * h) W₁ = W₁ from fun h' => hg (((hiff g h).1 h').2 hh), hg, hh]
            · simp only [(hiff g h).2 (iff_of_false hg hh), hg, hh, ite_true, ite_false,
                ← ofAdd_add]
              decide }
      have hker : ∀ g, g ∈ χ.ker → Φ g W₁ = W₁ := by
        intro g hg
        rw [MonoidHom.mem_ker] at hg
        by_contra h
        have : χ g = Multiplicative.ofAdd 1 := ite_eq_right h
        rw [this] at hg
        exact absurd hg (by decide)
      intro g
      have hcomm : commutator L ≤ χ.ker := Abelianization.commutator_subset_ker χ
      rw [Group.isPerfect_def.1 hperf] at hcomm
      exact hker g (hcomm (mem_top g))
  have hW₁X : W₁ ≤ Xbar := by
    rw [← hPmap]
    exact map_mono (hTsub Q₁ hQ₁).1
  have hinv : ∀ g : L, ∀ w ∈ W₁, (g : L ⧸ A) * w * (g : L ⧸ A)⁻¹ ∈ W₁ := by
    intro g w hw
    have h1 : (MulAut.conj (π g)).toMonoidHom w ∈ Φ g W₁ := ⟨w, hw, rfl⟩
    rw [hfix g] at h1
    exact h1
  rcases hirr W₁ hW₁X hinv with h | h
  · exact (hTsub Q₁ hQ₁).2.1 (hmap_bot Q₁ (hTsub Q₁ hQ₁).1 h)
  · exact (hTsub Q₁ hQ₁).2.2 (hmap_top Q₁ (hTsub Q₁ hQ₁).1 (h.trans hPmap.symm))

end CFSG.Quasithin.SteinbergBT
