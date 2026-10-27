module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Setup

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ]

namespace Lemma27

theorem exists_component_le_of_normal {X N : Subgroup Γ} (hX : IsDirectProduct (lcal X) X)
    (hNX : N ≤ X) (hN : X ≤ Subgroup.normalizer (N : Set Γ)) (hN1 : N ≠ ⊥) :
    ∃ J ∈ lcal X, J ≤ N := by
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hN1 ((Subgroup.eq_bot_iff_forall N).mpr hcon)
  have hnX : n ∈ X := hNX hnN
  obtain ⟨J, hJ, hcoord⟩ : ∃ J, ∃ hJ : J ∈ lcal X, hX.coord hJ ⟨n, hnX⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (⟨n, hnX⟩ : X) = 1 := hX.ext_coord fun D hD => by rw [map_one]; exact hcon D hD
    exact hn1 (congrArg Subtype.val this)
  obtain ⟨hJs, hJnc⟩ := simple_of_mem_lcal hJ
  have hNconj : ∀ u ∈ N, ∀ g ∈ X, g * u * g⁻¹ ∈ N := fun u hu g hg =>
    (Subgroup.mem_normalizer_iff.mp (hN hg) u).mp hu
  set d₀ : J := hX.coord hJ ⟨n, hnX⟩ with hd₀
  obtain ⟨t, htJ, ht⟩ : ∃ t ∈ J, t * (d₀ : Γ) ≠ (d₀ : Γ) * t := by
    by_contra hcon
    push Not at hcon
    refine hcoord (Subtype.ext ?_)
    exact AChief.eq_one_of_forall_commute hJs hJnc d₀.2 hcon
  have htX : t ∈ X := hX.le hJ htJ
  have hJconj : ∀ d ∈ J, ∀ g ∈ X, g * d * g⁻¹ ∈ J := fun d hd g hg =>
    (Subgroup.mem_normalizer_iff.mp (hX.le_normalizer hJ hg) d).mp hd
  have hw : n * t * n⁻¹ * t⁻¹ ∈ N ⊓ J := Subgroup.mem_inf.mpr
    ⟨by
      have h1 := mul_mem hnN (hNconj n⁻¹ (inv_mem hnN) t htX)
      simpa [mul_assoc] using h1,
     mul_mem (hJconj t htJ n hnX) (inv_mem htJ)⟩
  have hw1 : n * t * n⁻¹ * t⁻¹ ≠ 1 := by
    intro h
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    have hcm : (⟨n, hnX⟩ : X) * ⟨t, htX⟩ = ⟨t, htX⟩ * ⟨n, hnX⟩ := Subtype.ext h
    have h2 := congrArg (hX.coord hJ) hcm
    rw [map_mul, map_mul] at h2
    have h3 : hX.coord hJ ⟨t, htX⟩ = ⟨t, htJ⟩ := Subtype.ext (hX.coord_of_mem hJ htJ)
    rw [h3, ← hd₀] at h2
    exact ht (congrArg Subtype.val h2).symm
  have hnorm : ∀ u ∈ N ⊓ J, ∀ j ∈ J, j * u * j⁻¹ ∈ N ⊓ J := fun u hu j hj =>
    Subgroup.mem_inf.mpr
      ⟨hNconj u (Subgroup.mem_inf.mp hu).1 j (hX.le hJ hj),
        mul_mem (mul_mem hj (Subgroup.mem_inf.mp hu).2) (inv_mem hj)⟩
  refine ⟨J, hJ, ?_⟩
  rcases eq_bot_or_eq_of_conj_mem hJs inf_le_right hnorm with h | h
  · exact absurd (by have := h ▸ hw; exact Subgroup.mem_bot.mp this) hw1
  · exact fun x hx => (Subgroup.mem_inf.mp (h.symm ▸ hx : x ∈ N ⊓ J)).1

omit [Finite Γ] in
theorem normalizer_of_normal_normal {X K N : Subgroup Γ} (hX : IsDirectProduct (lcal X) X)
    (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set Γ)) : X ≤ Subgroup.normalizer (N : Set Γ) := by
  rw [← hX.sSup_eq]
  refine sSup_le fun J hJ => ?_
  obtain ⟨hJs, hJnc⟩ := simple_of_mem_lcal hJ
  have hJconj : ∀ d ∈ J, ∀ g ∈ X, g * d * g⁻¹ ∈ J := fun d hd g hg =>
    (Subgroup.mem_normalizer_iff.mp (hX.le_normalizer hJ hg) d).mp hd
  have hKconj : ∀ k ∈ K, ∀ g ∈ X, g * k * g⁻¹ ∈ K := fun k hk g hg =>
    (Subgroup.mem_normalizer_iff.mp (hXK hg) k).mp hk
  have hnorm : ∀ u ∈ J ⊓ K, ∀ j ∈ J, j * u * j⁻¹ ∈ J ⊓ K := fun u hu j hj =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hj (Subgroup.mem_inf.mp hu).1) (inv_mem hj),
      hKconj u (Subgroup.mem_inf.mp hu).2 j (hX.le hJ hj)⟩
  rcases eq_bot_or_eq_of_conj_mem hJs inf_le_left hnorm with h | h
  ·
    have hcomm : ∀ j ∈ J, ∀ k ∈ K, j * k = k * j := by
      intro j hj k hk
      have hmem : j * k * j⁻¹ * k⁻¹ ∈ J ⊓ K := Subgroup.mem_inf.mpr
        ⟨by
          have h1 := mul_mem hj (hJconj j⁻¹ (inv_mem hj) k (hKX hk))
          simpa [mul_assoc] using h1,
         mul_mem (hKconj k hk j (hX.le hJ hj)) (inv_mem hk)⟩
      rw [h, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
      exact hmem
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ j ∈ J, ∀ x ∈ N, j * x * j⁻¹ ∈ N := fun j hj x hx => by
      have h2 : j * x * j⁻¹ = x := by rw [hcomm j hj x (hNK hx)]; group
      rw [h2]
      exact hx
    refine ⟨key j hj x, fun hx => ?_⟩
    have := key j⁻¹ (inv_mem hj) _ hx
    simpa [mul_assoc] using this
  · have hJK : J ≤ K := by
      intro x hx
      exact (Subgroup.mem_inf.mp (h.symm ▸ hx : x ∈ J ⊓ K)).2
    exact hJK.trans hKN

omit [Finite Γ] in
theorem normalizer_of_isCharIn {K X : Subgroup Γ} (h : IsCharIn K X) :
    X ≤ Subgroup.normalizer (K : Set Γ) := by
  have key : ∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    have hkX : k ∈ X := h.1 hk
    have h1 : (⟨k, hkX⟩ : X) ∈ K.subgroupOf X := hk
    have h2 : (MulAut.conj (⟨g, hg⟩ : X)).toMonoidHom ⟨k, hkX⟩ ∈
        (K.subgroupOf X).map (MulAut.conj (⟨g, hg⟩ : X)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ h1
    rw [h.2 (MulAut.conj ⟨g, hg⟩)] at h2
    exact h2
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key g hg y hy, fun hy => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hy⟩

omit [Finite Γ] in
theorem le_normalizer_sup {X S T : Subgroup Γ} (hS : X ≤ Subgroup.normalizer (S : Set Γ))
    (hT : X ≤ Subgroup.normalizer (T : Set Γ)) :
    X ≤ Subgroup.normalizer ((S ⊔ T : Subgroup Γ) : Set Γ) := by
  have key : ∀ g ∈ X, ∀ y ∈ S ⊔ T, g * y * g⁻¹ ∈ S ⊔ T := by
    intro g hg y hy
    have hle : S ⊔ T ≤ (S ⊔ T).comap (MulAut.conj g).toMonoidHom :=
      sup_le (fun s hs => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hS hg) s).mp hs))
        (fun t ht => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hT hg) t).mp ht))
    exact hle hy
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key g hg y hy, fun hy => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hy⟩

theorem exists_mulEquiv_component_of_chief {X K M N : Subgroup Γ} (hss : IsSemisimple X)
    (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) (hMN : IsChiefFactorOf K M N)
    [(N.subgroupOf M).Normal] : ∃ J ∈ lcal X, Nonempty (↥J ≃* ↥M ⧸ N.subgroupOf M) := by
  have hX : IsDirectProduct (lcal X) X := hss.isDirectProduct_lcal
  obtain ⟨hNK, hMK, hNM, hmin⟩ := hMN
  have hMXn : X ≤ Subgroup.normalizer (M : Set Γ) :=
    normalizer_of_normal_normal hX hKX hXK hMK.1 hMK.2
  have hNXn : X ≤ Subgroup.normalizer (N : Set Γ) :=
    normalizer_of_normal_normal hX hKX hXK hNK.1 hNK.2
  have hMX : M ≤ X := hMK.1.trans hKX
  have hNX : N ≤ X := hNK.1.trans hKX
  have hNnorm : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hNXn
  have hpair := hss.isDirectPair_of_normal hNX hNnorm
  set C := X ⊓ Subgroup.centralizer (N : Set Γ) with hC
  set M₀ : Subgroup Γ := M ⊓ Subgroup.centralizer (N : Set Γ) with hM₀
  have hM₀X : M₀ ≤ X := inf_le_left.trans hMX
  have hM₀norm : X ≤ Subgroup.normalizer (M₀ : Set Γ) := by
    have key : ∀ g ∈ X, ∀ m ∈ M₀, g * m * g⁻¹ ∈ M₀ := by
      intro g hg m hm
      obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.mp hm
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hMXn hg) m).mp hmM, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hn' : g⁻¹ * n * g ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (hNXn (inv_mem hg)) n).mp hn
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hmC _ hn'
      calc n * (g * m * g⁻¹) = g * ((g⁻¹ * n * g) * m) * g⁻¹ := by group
        _ = g * (m * (g⁻¹ * n * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * m * g⁻¹) * n := by group
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => key g hg y hy, fun hy => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hy⟩
  have hM₀ne : M₀ ≠ ⊥ := by
    intro h
    refine hNM.not_ge fun m hm => ?_
    have hmX : m ∈ N ⊔ C := hpair.sup_eq ▸ hMX hm
    obtain ⟨n, hn, c, hc, rfl⟩ := (mem_sup_iff_of_commute hpair.commute).mp hmX
    have hcM : c ∈ M := by
      have : c = n⁻¹ * (n * c) := by group
      rw [this]
      exact mul_mem (inv_mem (hNM.le hn)) hm
    have hc0 : c ∈ M₀ := Subgroup.mem_inf.mpr ⟨hcM, (Subgroup.mem_inf.mp hc).2⟩
    rw [h, Subgroup.mem_bot] at hc0
    rw [hc0, mul_one]
    exact hn
  obtain ⟨J, hJ, hJM₀⟩ := exists_component_le_of_normal hX hM₀X hM₀norm hM₀ne
  have hJM : J ≤ M := hJM₀.trans inf_le_left
  have hJcen : ∀ x ∈ J, ∀ n ∈ N, n * x = x * n := fun x hx n hn =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hJM₀ hx)).2 n hn
  have hJN : J ⊓ N = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxJ, hxN⟩ := Subgroup.mem_inf.mp hx
    have : x ∈ N ⊓ C := Subgroup.mem_inf.mpr ⟨hxN, Subgroup.mem_inf.mpr
      ⟨hX.le hJ hxJ, (Subgroup.mem_inf.mp (hJM₀ hxJ)).2⟩⟩
    rwa [hpair.inf_eq_bot] at this
  have hJbot : J ≠ ⊥ := by
    intro h
    obtain ⟨-, x, hx, y, hy, hxy⟩ := simple_of_mem_lcal hJ
    rw [h, Subgroup.mem_bot] at hx
    exact hxy (by rw [hx, one_mul, mul_one])
  have hTM : N ⊔ J ≤ M := sup_le hNM.le hJM
  have hTnorm : IsNormalIn (N ⊔ J) K :=
    ⟨hTM.trans hMK.1, hKX.trans (le_normalizer_sup hNXn (hX.le_normalizer hJ))⟩
  have hMeq : N ⊔ J = M := by
    rcases hmin _ hTnorm le_sup_left hTM with h | h
    · refine absurd (eq_bot_iff.mpr fun x hx => ?_) hJbot
      have : x ∈ J ⊓ N := Subgroup.mem_inf.mpr ⟨hx, (le_sup_right.trans h.le) hx⟩
      rwa [hJN] at this
    · exact h
  let φ : ↥J →* ↥M ⧸ N.subgroupOf M :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hJM)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : Subgroup.inclusion hJM x ∈ N.subgroupOf M := (QuotientGroup.eq_one_iff _).mp hx
    have hxN : (x : Γ) ∈ N := hx'
    have : (x : Γ) ∈ J ⊓ N := Subgroup.mem_inf.mpr ⟨x.2, hxN⟩
    rw [hJN, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hmT : (m : Γ) ∈ N ⊔ J := hMeq ▸ m.2
    obtain ⟨n, hn, j, hj, hnj⟩ :=
      (mem_sup_iff_of_commute fun x hx y hy => hJcen y hy x hx).mp hmT
    refine ⟨⟨j, hj⟩, ?_⟩
    have h1 : (Subgroup.inclusion hJM ⟨j, hj⟩)⁻¹ * m ∈ N.subgroupOf M := by
      show j⁻¹ * (m : Γ) ∈ N
      rw [← hnj]
      have h2 : j⁻¹ * (n * j) = n := by
        rw [hJcen j hj n hn]
        group
      rw [h2]
      exact hn
    exact QuotientGroup.eq.mpr h1
  exact ⟨J, hJ, ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩⟩

theorem isCyclic_of_mulEquiv {J Q : Type*} [Group J] [Group Q] (e : J ≃* Q) {p : ℕ}
    (h : ∀ P : Subgroup (MulAut J), IsPGroup p P → IsCyclic P)
    (P : Subgroup (MulAut Q)) (hP : IsPGroup p P) : IsCyclic P := by
  have hc : IsCyclic ((P.comap (MulAut.congr e).toMonoidHom : Subgroup (MulAut J))) :=
    h _ (hP.comap_of_injective _ (MulAut.congr e).injective)
  exact isCyclic_of_surjective ((MulAut.congr e).toMonoidHom.subgroupComap P)
    (MonoidHom.subgroupComap_surjective _ _ (MulAut.congr e).surjective)

theorem outSectionsCyclic_of_isSemisimple_of_aut {p : ℕ} {X : Subgroup Γ} (hss : IsSemisimple X)
    (h : ∀ J ∈ lcal X, ∀ P : Subgroup (MulAut ↥J), IsPGroup p P → IsCyclic P) :
    OutSectionsCyclic p X := by
  intro K L M N hK hL hLK hMN hLN _ P hP
  obtain ⟨J, hJ, ⟨e⟩⟩ := exists_mulEquiv_component_of_chief hss hK.1 (normalizer_of_isCharIn hK) hMN
  exact isCyclic_of_mulEquiv e (h J hJ) P hP

end Lemma27

theorem outSectionsCyclic_of_isSemisimple
    {p : ℕ} (hp : p.Prime) {X : Subgroup Γ}
    (hss : IsSemisimple X) (hnear : signalizerNearPSolvable p ↥X) : OutSectionsCyclic p X := by
  refine Lemma27.outSectionsCyclic_of_isSemisimple_of_aut hss fun J hJ P hP => ?_
  obtain ⟨hJX, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  exact near_aut_sylow_cyclic
    ⟨hp, hs, exists_mul_ne_of_not_isMulCommutative hnc, signalizerNearPSolvable_of_le hJX hnear⟩
    P hP

end CFSG.SignalizerFunctorTheorem.McBride.Near
