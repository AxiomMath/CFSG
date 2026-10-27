module

public import CFSG.Quasithin.Background.SmithB45HatA6Mono
public import CFSG.Quasithin.Background.SmithB45HatA6Six
public import CFSG.Quasithin.Background.SmithB45HatA6Out
public import CFSG.Quasithin.Background.SmithB42HatA6Off
public import CFSG.Quasithin.Background.SmithB45Families

public section

namespace CFSG.Quasithin

namespace B45HatA6

open Equiv

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

omit [Finite V] in
theorem exists_proj (hP : B42TypeHatA6 ↥L) :
    ∃ π : ↥L →* Perm (Fin 6), (∀ l, π l ∈ alternatingGroup (Fin 6)) ∧
      (∀ σ ∈ alternatingGroup (Fin 6), ∃ l, π l = σ) ∧
      ∀ l, π l = 1 → l ∈ Subgroup.center ↥L := by
  obtain ⟨-, -, ⟨e⟩⟩ := hP
  refine ⟨(alternatingGroup (Fin 6)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))),
    fun l => (e (QuotientGroup.mk l)).2, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨y, hy⟩ := e.surjective ⟨σ, hσ⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨l, ?_⟩
    change ((e (QuotientGroup.mk l) : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = σ
    rw [hy]
  · intro l hl
    have h1 : e (QuotientGroup.mk l) = 1 := Subtype.ext hl
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1

omit [Finite V] in
theorem false_of_eight (hP : B42TypeHatA6 ↥L) {A : Subgroup (MulAut V)} (hAL : A ≤ L)
    (hAe : IsElemAbelian2 A) (h8 : Nat.card A = 8) : False := by
  classical
  obtain ⟨π, hπA, -, hπker⟩ := exists_proj hP
  have hZ3 := hP.2.1
  set A' : Subgroup ↥L := A.subgroupOf L with hA'
  have hψ : Function.Injective (π.comp A'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (Subtype.ext
      (HatA6.eq_one_of_mem_center hZ3 (a : ↥L).2 (hπker _ ha) (hAe.2 _ a.2)))
  set P : Subgroup (Perm (Fin 6)) := A'.map π with hPdef
  have hP8 : Nat.card P = 8 := by
    have hr : P = (π.comp A'.subtype).range := by
      rw [hPdef, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, ← h8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hPA : P ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨a, -, rfl⟩
    exact hπA a
  have hD8 : Nat.card (P.subgroupOf (alternatingGroup (Fin 6))) = 8 := by
    rw [← hP8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := B42Alt6.not_comm_of_card_eight _ hD8
  apply hxy
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_subgroupOf.1 hx
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_subgroupOf.1 hy
  change (x : Perm (Fin 6)) * y = y * x
  rw [← hax, ← hby, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hAe.1 _ ha _ hb)

theorem false_of_invol (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L) (hP : B42TypeHatA6 ↥L)
    (hcard : Nat.card V = 2 ^ 12) {t : ↥L} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 4) : False := by
  classical
  obtain ⟨π, hπA, hπs, hπker⟩ := exists_proj hP
  have hZ3 := hP.2.1
  obtain ⟨zL, hcen, h3, -, -⟩ := HatA6.exists_center_gen hHyp hP
  have hcen3 := pow_three_of_mem_center hcen h3
  have hπt1 : π t ≠ 1 := fun h => ht1 (Subtype.ext (HatA6.eq_one_of_mem_center hZ3 t.2
    (hπker t h) (by rw [pow_two]; exact congrArg Subtype.val ht2)))
  have hπt2 : π t * π t = 1 := by rw [← map_mul, ht2, map_one]
  obtain ⟨ha2, -, hab, haA, -, -, ha1, -, hne⟩ := aY_bY false
  obtain ⟨d, hd, hdt⟩ := S143.alt6_invol_conj aY (π t) haA (hπA t) ha1 hπt1 ha2 hπt2
  obtain ⟨hcA, hc⟩ : (swap (1 : Fin 6) 2 * swap 2 3) ∈ alternatingGroup (Fin 6) ∧
      (swap (1 : Fin 6) 2 * swap 2 3) * aY * (swap 1 2 * swap 2 3)⁻¹ = bY false := by
    simp only [Perm.mem_alternatingGroup]
    decide
  obtain ⟨g, hg⟩ := hπs (d * (swap 1 2 * swap 2 3) * d⁻¹) (mul_mem (mul_mem hd hcA) (inv_mem hd))
  obtain ⟨s, hs⟩ : ∃ s : ↥L, s = g * t * g⁻¹ := ⟨_, rfl⟩
  have hπs' : π s = d * bY false * d⁻¹ := by
    rw [hs, map_mul, map_mul, map_inv, hg, ← hdt, ← hc]
    group
  have hs2 : s * s = 1 := by
    rw [hs]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hcc : t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center ↥L := hπker _ (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπs', ← hdt]
    calc d * aY * d⁻¹ * (d * bY false * d⁻¹) * (d * aY * d⁻¹)⁻¹ * (d * bY false * d⁻¹)⁻¹ =
        d * (aY * bY false) * aY⁻¹ * (bY false)⁻¹ * d⁻¹ := by group
      _ = 1 := by rw [hab]; group)
  have hts : t * s = s * t := comm_of_commutator_mem_center hs2 hcc (hcen3 _ hcc)
  have hst : t ≠ s := by
    intro h
    apply hne
    have h1 : π t = π s := by rw [h]
    rw [hπs', ← hdt] at h1
    calc aY = d⁻¹ * (d * aY * d⁻¹) * d := by group
      _ = d⁻¹ * (d * bY false * d⁻¹) * d := by rw [h1]
      _ = bY false := by group
  have hs1 : s ≠ 1 := by
    intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [← hs, h]; group
  set E : Subgroup (MulAut V) := Subgroup.closure {(t : MulAut V), (s : MulAut V)} with hE
  have hEL : E ≤ L := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact t.2
    · exact s.2
  have hEe : IsElemAbelian2 E := isElemAbelian2_closure_pair (congrArg Subtype.val ht2)
    (congrArg Subtype.val hs2) (congrArg Subtype.val hts)
  have hE4 : Nat.card E = 4 := card_closure_pair_eq_four (congrArg Subtype.val ht2)
    (congrArg Subtype.val hs2) (congrArg Subtype.val hts) (fun h => ht1 (Subtype.ext h))
    (fun h => hs1 (Subtype.ext h)) (fun h => hst (Subtype.ext h))
  have hzs : Subgroup.zpowers (s : MulAut V) =
      (Subgroup.zpowers (t : MulAut V)).map (MulAut.conj (g : MulAut V)).toMonoidHom := by
    rw [MonoidHom.map_zpowers, hs]
    rfl
  have hidxs : (fixV (Subgroup.zpowers (s : MulAut V))).index ≤ 4 := by
    rw [hzs, index_fixV_map_conj]
    exact hidx
  have hle : fixV (Subgroup.zpowers (t : MulAut V)) ⊓ fixV (Subgroup.zpowers (s : MulAut V)) ≤
      fixV E := by
    rintro w ⟨h1, h2⟩
    rw [hE, mem_fixV_closure_pair]
    exact ⟨HatA6.mem_fixV_zpowers_iff.1 h1, HatA6.mem_fixV_zpowers_iff.1 h2⟩
  have hidxE : (fixV E).index ≤ 16 := by
    calc (fixV E).index ≤ (fixV (Subgroup.zpowers (t : MulAut V)) ⊓
          fixV (Subgroup.zpowers (s : MulAut V))).index := Subgroup.index_antitone hle
      _ ≤ (fixV (Subgroup.zpowers (t : MulAut V))).index *
          (fixV (Subgroup.zpowers (s : MulAut V))).index := Subgroup.index_inf_le
      _ ≤ 4 * 4 := Nat.mul_le_mul hidx hidxs
      _ = 16 := by norm_num
  exact false_of_four hV hHyp hP hcard hEL hEe hE4 hidxE

theorem false_of_inverts (hHyp : B4Hyp G L) (hcard : Nat.card V = 2 ^ 12)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hAe : IsElemAbelian2 A) (hA8 : Nat.card A ≤ 8)
    (hidx : (fixV A).index ≤ Nat.card A ^ 2) {zL : ↥L}
    (hcen : Subgroup.center ↥L = Subgroup.zpowers zL) (h3 : (zL : MulAut V) ^ 3 = 1)
    (hz1 : (zL : MulAut V) ≠ 1) (hfp : ∀ v : V, (zL : MulAut V) v = v → v = 1)
    {t : MulAut V} (htA : t ∈ A) (htz : t * zL ≠ zL * t) : False := by
  classical
  set z : MulAut V := (zL : MulAut V) with hzdef
  have hGN := HatA6.le_normalizer_of_b4Hyp hHyp
  have ht2 : t * z = z * z * t :=
    (HatA6.conj_z_cases hcen h3 hz1 (hGN (hAG htA))).resolve_left htz
  have htz' : ∀ v, t (z v) = z (z (t v)) := fun v => congrArg (fun y : MulAut V => y v) ht2
  set B₀ := A ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) with hB₀
  have hB₀B : B₀ ≤ A := inf_le_left
  have hbt : ∀ b ∈ A, b ∉ B₀ → b * t ∈ B₀ := by
    intro b hb hb0
    have hbz : b * z = z * z * b := by
      rcases HatA6.conj_z_cases hcen h3 hz1 (hGN (hAG hb)) with h | h
      · exact absurd ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 h⟩ hb0
      · exact h
    refine ⟨A.mul_mem hb htA, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hz3 : z * z * z = 1 := by rw [← pow_three']; exact h3
    calc b * t * z = b * (t * z) := by group
      _ = b * (z * z * t) := by rw [ht2]
      _ = (b * z) * z * t := by group
      _ = (z * z * b) * z * t := by rw [hbz]
      _ = z * z * (b * z) * t := by group
      _ = z * z * (z * z * b) * t := by rw [hbz]
      _ = z * (z * z * z) * b * t := by group
      _ = z * (b * t) := by rw [hz3]; group
  have hcardB₀ : Nat.card A ≤ 2 * Nat.card B₀ := by
    let f : ↥A → ↥B₀ ⊕ ↥B₀ := fun b =>
      if hb : (b : MulAut V) ∈ B₀ then Sum.inl ⟨b, hb⟩
      else Sum.inr ⟨b * t, hbt b b.2 hb⟩
    have hf : Function.Injective f := by
      intro b b' h
      by_cases h1 : (b : MulAut V) ∈ B₀ <;> by_cases h2 : (b' : MulAut V) ∈ B₀
      · simp only [f, h1, h2, dite_true, Sum.inl.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext h
      · simp [f, h1, h2] at h
      · simp [f, h1, h2] at h
      · simp only [f, h1, h2, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext (mul_right_cancel h)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum, ← two_mul] at this
  have hfixA : fixV A = fixV B₀ ⊓ fixV (Subgroup.zpowers t) := by
    ext v
    constructor
    · intro hv
      exact ⟨fun b hb => hv b (hB₀B hb), (HatA6.mem_fixV_zpowers_iff).2 (hv t htA)⟩
    · rintro ⟨hv0, hvt⟩ b hb
      have hvt' : t v = v := (HatA6.mem_fixV_zpowers_iff).1 hvt
      by_cases hb0 : b ∈ B₀
      · exact hv0 b hb0
      · have ht22 : t * t = 1 := by rw [← pow_two]; exact hAe.2 t htA
        have h1 := hv0 _ (hbt b hb hb0)
        calc b v = (b * t * t) v := by rw [mul_assoc, ht22, mul_one]
          _ = (b * t) (t v) := rfl
          _ = v := by rw [hvt', h1]
  have hzU : ∀ u ∈ fixV B₀, z u ∈ fixV B₀ := by
    intro u hu b hb
    have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.1 hb.2
    have := congrArg (fun y : MulAut V => y u) hbz
    change b (z u) = z (b u) at this
    rw [this, hu b hb]
  have hdesc := HatA6.card_sq_le_of_semilinear hfp htz' hzU
  rw [← hfixA] at hdesc
  have e1 := (fixV A).card_mul_index
  have hc0 : Nat.card (fixV B₀) ≤ 2 ^ 12 := hcard ▸ Subgroup.card_le_card_group _
  have h1 : 2 ^ 12 ≤ Nat.card (fixV A) * Nat.card A ^ 2 := by
    rw [← hcard, ← e1]
    exact Nat.mul_le_mul_left _ hidx
  have hc64 : Nat.card (fixV A) ≤ 64 := by nlinarith
  have hA8' : 8 ≤ Nat.card A := by nlinarith
  have hc64' : 64 ≤ Nat.card (fixV A) := by
    have : Nat.card A = 8 := le_antisymm hA8 hA8'
    rw [this] at h1
    omega
  have htop : fixV B₀ = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hcard]
    nlinarith
  have hB₀1 : Nat.card B₀ = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    exact (htop ▸ Subgroup.mem_top v : v ∈ fixV B₀) b hb
  omega

end B45HatA6

open B45HatA6 in
theorem asB45HatA6_holds : AsB45HatA6 := by
  intro V _ _ hV G L hHyp hP h2
  classical
  obtain ⟨A, ⟨hAG, hA1, hAe⟩, -, hidx⟩ := B45Alt.exists_cubic_of_qhatOf_le_two hV h2
  obtain ⟨r, m, hr, hr1, hr3, hmr, l, -, hle⟩ := HatA6.short_generation hHyp hP hAG hA1 hAe
  have hVle : Nat.card V ≤ 2 ^ 12 := by
    calc Nat.card V ≤ (fixV A).index ^ m :=
          HatA6.card_le_pow_of_le_closure (HatA6.fixV_eq_bot_of_b4Hyp hHyp) l hle
      _ ≤ (Nat.card A ^ 2) ^ m := Nat.pow_le_pow_left hidx m
      _ = 2 ^ (2 * (m * r)) := by rw [hr, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk := card_eq_two_pow_rk hV
  have h9 := card_mod_nine hHyp hP
  have hk12 : rk V ≤ 12 := by
    rw [hk] at hVle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hVle
  obtain ⟨zL, hcen, h3, hz1, hfp⟩ := HatA6.exists_center_gen hHyp hP
  have hk' : rk V = 0 ∨ rk V = 6 ∨ rk V = 12 := by
    rw [hk] at h9
    revert h9
    interval_cases rk V <;> norm_num
  rcases hk' with h0 | h6 | h12
  ·
    exfalso
    apply hz1
    have hsub : Subsingleton V := Finite.card_le_one_iff_subsingleton.1 (by rw [hk, h0]; norm_num)
    exact MulEquiv.ext fun v => Subsingleton.elim _ _
  · exact qhatOf_le_one_of_card hV hHyp hP (by rw [hk, h6])
  · exfalso
    have hcard : Nat.card V = 2 ^ 12 := by rw [hk, h12]
    have hA8 : Nat.card A ≤ 8 := by
      rw [hr]
      calc 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hr3
        _ = 8 := by norm_num
    by_cases hcomm : ∀ a ∈ A, a * (zL : MulAut V) = (zL : MulAut V) * a
    · have hAL : A ≤ L := fun a ha => mem_of_commute_center hHyp hP hcen (hAG ha)
        (by rw [← pow_two]; exact hAe.2 a ha) (hcomm a ha)
      interval_cases r
      ·
        obtain ⟨⟨t, htA⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
        have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
        have hidx' : (fixV (Subgroup.zpowers t)).index ≤ 4 := by
          refine (Subgroup.index_antitone (B1.fixV_le_fixV ?_)).trans (hidx.trans ?_)
          · exact (Subgroup.zpowers_le).2 htA
          · rw [hr]; norm_num
        have ht2 : (⟨t, hAL htA⟩ : ↥L) * ⟨t, hAL htA⟩ = 1 :=
          Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact hAe.2 t htA)
        exact false_of_invol hV hHyp hP hcard ht2 (fun h => ht1' (congrArg Subtype.val h))
          hidx'
      ·
        exact false_of_four hV hHyp hP hcard hAL hAe hr (by rw [hr] at hidx; simpa using hidx)
      ·
        exact false_of_eight hP hAL hAe hr
    · push Not at hcomm
      obtain ⟨t, htA, htz⟩ := hcomm
      exact false_of_inverts hHyp hcard hAG hAe hA8 hidx hcen h3 hz1 hfp htA htz

end CFSG.Quasithin
