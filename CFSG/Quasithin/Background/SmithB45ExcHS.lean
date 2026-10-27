module

public import CFSG.Quasithin.Background.SmithB45ExcHSSyl
public import CFSG.Quasithin.Background.SmithB45ExcHSDisp
public import CFSG.Quasithin.Background.SmithB45ExcHSRuDisp

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.Quasithin.B45Exc.Tab CFSG.Quasithin.B45Exc.HSRu CFSG.Quasithin.B45Exc.HS
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Bridge.HSExcl CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.Blueprint

namespace HS

section Cosets

theorem hsP_index_two : (hsP.subgroupOf hsR).index = 2 := by
  have h1 := (hsP.subgroupOf hsR).card_mul_index
  have h2 : Nat.card (hsP.subgroupOf hsR) = 44352000 := by
    rw [← card_hsP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsP_le_hsR).toEquiv
  rw [h2, hs_normalizing_model.2.2.2.2.2.2.2.2.1] at h1
  omega

theorem inv_mul_mem_hsP {x y : Equiv.Perm (Fin 3850)} (hx : x ∈ hsR) (hy : y ∈ hsR)
    (hxP : x ∉ hsP) (hyP : y ∉ hsP) : x⁻¹ * y ∈ hsP := by
  have h := (Subgroup.mul_mem_iff_of_index_two hsP_index_two (a := (⟨x, hx⟩ : ↥hsR)⁻¹)
    (b := ⟨y, hy⟩)).2
  simp only [Subgroup.mem_subgroupOf, inv_mem_iff] at h
  exact h ⟨fun h' => absurd h' hxP, fun h' => absurd h' hyP⟩

theorem exists_outer_mem_hsS : ∃ u ∈ hsS, u ∉ hsP := by
  by_contra h
  push Not at h
  have hle : hsS ≤ hsP := fun u hu => h u hu
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hs_involution_centralizers.2.1, card_hsP] at hdvd
  norm_num at hdvd

theorem hsR_eq_mul (r : Equiv.Perm (Fin 3850)) (hr : r ∈ hsR) :
    ∃ u ∈ hsS, ∃ p ∈ hsP, r = u * p := by
  by_cases hrP : r ∈ hsP
  · exact ⟨1, hsS.one_mem, r, hrP, by group⟩
  · obtain ⟨u, hu, huP⟩ := exists_outer_mem_hsS
    exact ⟨u, hu, u⁻¹ * r, inv_mul_mem_hsP (hs_involution_centralizers.1 hu) hr huP hrP,
      by group⟩

theorem card_hsS_eq : Nat.card hsS = 2 ^ (Nat.card hsR).factorization 2 := by
  rw [hs_involution_centralizers.2.1, hs_normalizing_model.2.2.2.2.2.2.2.2.1,
    show (88704000 : ℕ) = 2 ^ 10 * 86625 by norm_num,
    Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 86625)]
  simp

end Cosets

section Inv

variable
  {W : Type} [CommGroup W] [Finite W]

theorem hs_disp_inner (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (ψ : Lift L E hsR hsP) (eqv : ↥L ≃* NativeSporadic.Carrier .HS) (b : ↥(L ⊔ E))
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbP : ψ.toG b ∈ hsP) :
    2 ^ 8 ≤ (fixV (Subgroup.zpowers (b : MulAut W))).index := by
  have hbR : ψ.toG b ∈ hsR := (ψ.hom b).2
  have hb2' : ψ.toG b * ψ.toG b = 1 := by rw [← map_mul, hb2, map_one]
  have hb1' : ψ.toG b ≠ 1 := fun h => hb1 (ψ.toG_injective (by rw [h, map_one]))
  obtain ⟨g, hg, k, hk, hbk⟩ := hs_inv_conj hbR hb2' hb1'
  have htP : hsT k ∈ hsP := by
    have : hsT k = g⁻¹ * ψ.toG b * g := by rw [hbk]; group
    rw [this]
    exact hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) hbP) hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact hs_disp_2A hW ψ eqv b hg hbk
  · exact le_trans (by norm_num) (hs_disp_2BD hW ψ b hg (Or.inl rfl) hbk)
  · exact absurd htP hsT_not_mem_P.1
  · exact absurd htP hsT_not_mem_P.2

theorem hs_disp_fix (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (ψ : Lift L E hsR hsP) (b : ↥(L ⊔ E)) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hfix : (fixFinset (ψ.toG b)).card = 30 ∨ (fixFinset (ψ.toG b)).card = 46) :
    2 ^ 10 ≤ (fixV (Subgroup.zpowers (b : MulAut W))).index := by
  have hbR : ψ.toG b ∈ hsR := (ψ.hom b).2
  have hb2' : ψ.toG b * ψ.toG b = 1 := by rw [← map_mul, hb2, map_one]
  have hb1' : ψ.toG b ≠ 1 := fun h => hb1 (ψ.toG_injective (by rw [h, map_one]))
  obtain ⟨-, h30, h46, -⟩ := hs_inv_of_fix hbR hb2' hb1'
  rcases hfix with h | h
  · obtain ⟨g, hg, hbg⟩ := h30 h
    exact hs_disp_2BD hW ψ b hg (Or.inl rfl) hbg
  · obtain ⟨g, hg, hbg⟩ := h46 h
    exact hs_disp_2BD hW ψ b hg (Or.inr rfl) hbg

end Inv

theorem mem_hsP_of_fix
    {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsR) (h2 : x * x = 1) (h1 : x ≠ 1)
    (hfix : (fixFinset x).card = 170 ∨ (fixFinset x).card = 30) : x ∈ hsP := by
  obtain ⟨h170, h30, -, -⟩ := hs_inv_of_fix hx h2 h1
  rcases hfix with h | h
  · obtain ⟨g, hg, hxg⟩ := h170 h
    rw [hxg]
    exact hsP.mul_mem (hsP.mul_mem hg hsT_mem_P.1) (hsP.inv_mem hg)
  · obtain ⟨g, hg, hxg⟩ := h30 h
    rw [hxg]
    exact hsP.mul_mem (hsP.mul_mem hg hsT_mem_P.2) (hsP.inv_mem hg)

end HS

open HS in
theorem sporadicExclusion2F_HS :
    SporadicExclusion2F .HS := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel
  have hcent : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_cover hW hq.1 hirr e fun E _ _ _ π hπ hC hodd => hs_cover E π hπ hC hodd
  set eqv := redEquiv e hcent with heqv
  have hdim : 2 ^ 20 ≤ Nat.card W := by
    let σ : NativeSporadic.Carrier .HS →* MulAut W := L.subtype.comp eqv.symm.toMonoidHom
    exact hs_dim W hW σ (fun a b hab => eqv.symm.injective (Subtype.ext hab))
  have : Nontrivial (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.fam_hs_simplicity.2.1
  have hL : L ≠ ⊥ := by
    intro h
    obtain ⟨s, hs⟩ := exists_ne (1 : NativeSporadic.Carrier .HS)
    obtain ⟨l, rfl⟩ := redHom_surjective L e s
    apply hs
    have hall : ∀ x ∈ L, x = 1 := fun x hx => by
      rw [h] at hx
      exact Subgroup.mem_bot.1 hx
    have : l = 1 := Subtype.ext (hall l l.2)
    rw [this, map_one]
  obtain ⟨Φ, hΦ⟩ := hs_aut_model
  set ψ : Lift L E hsR hsP := Lift.ofAut hW hq.1 hirr hE hEel e hcent hsP_le_hsR Φ hsEquivC hΦ
  obtain ⟨l, hl, hlU⟩ :=
    ψ.exists_conj_mem hEel hs_involution_centralizers.1 card_hsS_eq hsR_eq_mul
  set E' : Subgroup (MulAut W) := E.map (MulAut.conj l).toMonoidHom with hE'
  have hlN : l ∈ Subgroup.normalizer (L : Set (MulAut W)) := Subgroup.le_normalizer hl
  have hE'N : E' ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hlN (hE hx))
      ((Subgroup.normalizer _).inv_mem hlN)
  have hE'el : IsElemAbelian2 E' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show l * x * l⁻¹ * (l * y * l⁻¹) = l * (x * y) * l⁻¹ by group, hEel.1 x hx y hy]
      group
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow, hEel.2 x hx]
      group
  have hidx : (fixV E').index = (fixV E).index := index_fixV_map_conj E l
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj l).injective
  have hE'LE : ∀ x ∈ E', x ∈ L ⊔ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_sup hl hx
  set B : Subgroup (Equiv.Perm (Fin 3850)) := (E'.subgroupOf (L ⊔ E)).map ψ.toG with hB
  have hBmem : ∀ y, y ∈ B ↔ ∃ x : ↥(L ⊔ E), (x : MulAut W) ∈ E' ∧ ψ.toG x = y := by
    intro y
    simp [hB, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hBS : B ≤ hsS := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hBmem y).1 hy
    obtain ⟨z, hz, hzx⟩ := hx
    have : x = ⟨l * z * l⁻¹, conj_mem_sup hl hz⟩ := Subtype.ext hzx.symm
    rw [this]
    exact hlU z hz
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (hBmem x).1 hx
    obtain ⟨b, hb, rfl⟩ := (hBmem y).1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE'el.1 _ ha _ hb)
  have hsq' : ∀ x : ↥(L ⊔ E), (x : MulAut W) ∈ E' → x * x = 1 := fun x hx =>
    Subtype.ext (by simpa [sq] using hE'el.2 _ hx)
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hBmem x).1 hx
    rw [← map_mul, hsq' a ha, map_one]
  have hBcard : Nat.card B = Nat.card E := by
    rw [hB, Subgroup.card_map_of_injective ψ.toG_injective, ← hcardE']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'LE).toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpE : IsPGroup 2 E := by
    intro x
    exact ⟨1, Subtype.ext (by simpa [pow_one] using hEel.2 x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpE
  have hk5 : k ≤ 5 := by
    have := hs_syl_card_le B hBS hBcomm hBsq
    rw [hBcard, hk] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  refine weight2_lt_of_lt_index E ?_
  rw [← hidx, hk, ← pow_mul]
  have hne : E' ≠ ⊥ := by
    intro h
    apply hEne
    have h1 : Nat.card E' = 1 := by rw [h, Subgroup.card_bot]
    rw [hcardE'] at h1
    exact Subgroup.card_eq_one.1 h1
  have hidxle : ∀ x : ↥(L ⊔ E), (x : MulAut W) ∈ E' →
      (fixV (Subgroup.zpowers (x : MulAut W))).index ≤ (fixV E').index :=
    fun x hx => index_zpowers_le_index E' hx
  have hsqW : ∀ x : ↥(L ⊔ E), (x : MulAut W) ∈ E' → (x : MulAut W) ≠ 1 → x ≠ 1 :=
    fun x _ hx h => hx (by rw [h]; rfl)
  have hinner : 4 ≤ Nat.card E →
      ∃ b : ↥(L ⊔ E), (b : MulAut W) ∈ E' ∧ b ≠ 1 ∧ ψ.toG b ∈ hsP := by
    intro h4
    set BR : Subgroup ↥hsR := (E'.subgroupOf (L ⊔ E)).map ψ.hom with hBR
    have hBR4 : 4 ≤ Nat.card BR := by
      rw [hBR, Subgroup.card_map_of_injective ψ.inj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'LE).toEquiv, hcardE']
      exact h4
    obtain ⟨x, hxB, hx1, hxN⟩ := exists_mem_of_index_two (le_of_eq hsP_index_two) hBR4
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hxB
    exact ⟨b, Subgroup.mem_subgroupOf.1 hb, fun h => hx1 (by rw [h, map_one]),
      Subgroup.mem_subgroupOf.1 hxN⟩
  have hfix1 : (fixFinset (1 : Equiv.Perm (Fin 3850))).card = 3850 := by
    simp [fixFinset]
  have hne1 : ∀ x : ↥(L ⊔ E), ∀ n : ℕ, n ≠ 3850 → (fixFinset (ψ.toG x)).card = n → x ≠ 1 := by
    intro x n hn hx h
    rw [h, map_one, hfix1] at hx
    exact hn hx.symm
  interval_cases k
  ·
    exact absurd (Subgroup.card_eq_one.1 hk) hEne
  ·
    obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have h5 := hs_disp_all hW hq.1 hirr hE'N hE'el e hcent hbE hb1'
    have := (index_zpowers_le_index E' hbE)
    omega
  ·
    obtain ⟨b, hbE', hb1, hbP⟩ := hinner (by rw [hk]; norm_num)
    have h8 := hs_disp_inner hW ψ eqv b (hsq' b hbE') hb1 hbP
    have := hidxle b hbE'
    omega
  ·
    obtain ⟨b, hbE', hb1, hbP⟩ := hinner (by rw [hk]; norm_num)
    have h8 := hs_disp_inner hW ψ eqv b (hsq' b hbE') hb1 hbP
    have := hidxle b hbE'
    omega
  ·
    rcases hs_syl_four B hBS hBcomm hBsq (by rw [hBcard, hk]) with
      ⟨x, hxB, hx1, hfix⟩ | ⟨G, hG, hgen⟩
    · obtain ⟨y, hyE', rfl⟩ := (hBmem x).1 hxB
      have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
      have h10 := hs_disp_fix hW ψ y (hsq' y hyE') hy1 hfix
      have := hidxle y hyE'
      omega
    · obtain ⟨h, -, hLE⟩ := ψ.le_sup_of_le_closure hG hgen
      have h10 := le_of_two_pow_le_sq (k := 10)
        (hdim.trans (card_le_index_sq_of_le_sup hirr hL hLE))
      omega
  ·
    obtain ⟨⟨G, hG, hgen⟩, ⟨d, hdB, c, hcB, e1, he1B, e2, he2B, hfd, hfc, hfe1, hfe2, G', hG',
      hGc, h5, h1⟩⟩ := hs_syl_five B hBS hBcomm hBsq (by rw [hBcard, hk])
    obtain ⟨h, -, hLE⟩ := ψ.le_sup_of_le_closure hG hgen
    have hsq2 := card_le_index_sq_of_le_sup hirr hL hLE
    by_contra hcon
    push Not at hcon
    have hW20 : Nat.card W = 2 ^ 20 := by
      refine le_antisymm (hsq2.trans ?_) hdim
      calc (fixV E').index ^ 2 ≤ (2 ^ 10) ^ 2 := Nat.pow_le_pow_left hcon 2
        _ = 2 ^ 20 := by norm_num
    obtain ⟨d', hd'E, rfl⟩ := (hBmem d).1 hdB
    obtain ⟨c', hc'E, rfl⟩ := (hBmem c).1 hcB
    obtain ⟨e1', he1E, rfl⟩ := (hBmem e1).1 he1B
    obtain ⟨e2', he2E, rfl⟩ := (hBmem e2).1 he2B
    obtain ⟨g', hg'L, hg'G⟩ := ψ.surj G' hG'
    have hg'G' : ψ.toG g' = G' := hg'G
    have hd10 := hs_disp_fix hW ψ d' (hsq' d' hd'E) (hne1 d' 46 (by norm_num) hfd) (Or.inr hfd)
    have hdisp : (fixV E').index ≤ (fixV (Subgroup.zpowers (d' : MulAut W))).index :=
      hcon.trans hd10
    have hgc : (g' : MulAut W) * c' = c' * g' := by
      have : g' * c' = c' * g' := ψ.toG_injective (by rw [map_mul, map_mul, hg'G']; exact hGc)
      exact congrArg Subtype.val this
    have hquad := index_fixV_le_card_fixV hW hE'el hd'E hc'E he1E he2E hgc hdisp
    have hc'1 : (c' : MulAut W) ≠ 1 := by
      have := hne1 c' 350 (by norm_num) hfc
      exact fun h => this (Subtype.ext h)
    have hc5 := hs_disp_all hW hq.1 hirr hE'N hE'el e hcent hc'E hc'1
    have hcm := Subgroup.card_mul_index (fixV (Subgroup.zpowers (c' : MulAut W)))
    set y : ↥(L ⊔ E) := g' * e1' * g'⁻¹ * e2' with hy
    have hyG : ψ.toG y = G' * ψ.toG e1' * G'⁻¹ * ψ.toG e2' := by
      rw [hy, map_mul, map_mul, map_mul, map_inv, hg'G']
    have he1ne : ψ.toG e1' ≠ 1 := by
      intro h
      rw [h, hfix1] at hfe1
      omega
    have he2ne : ψ.toG e2' ≠ 1 := by
      intro h
      rw [h, hfix1] at hfe2
      omega
    have he1P : ψ.toG e1' ∈ hsP :=
      mem_hsP_of_fix (ψ.hom e1').2 (by rw [← map_mul, hsq' e1' he1E, map_one]) he1ne hfe1
    have he2P : ψ.toG e2' ∈ hsP :=
      mem_hsP_of_fix (ψ.hom e2').2 (by rw [← map_mul, hsq' e2' he2E, map_one]) he2ne hfe2
    have hyP : ψ.toG y ∈ hsP := by
      rw [hyG]
      exact hsP.mul_mem (hsP.mul_mem (hsP.mul_mem hG' he1P) (hsP.inv_mem hG')) he2P
    have hyL : (y : MulAut W) ∈ L := ψ.mem_of_mem hyP
    have hy5 : (y : MulAut W) ^ 5 = 1 := by
      have : y ^ 5 = 1 := ψ.toG_injective (by rw [map_pow, hyG, h5, map_one])
      rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
    have hy1 : (y : MulAut W) ≠ 1 := by
      intro hy1
      apply h1
      rw [← hyG, show y = 1 from Subtype.ext hy1, map_one]
    have h16 := hs_two_pow_sixteen hW eqv hyL hy5 hy1
    have hyW : (y : MulAut W) = (g' : MulAut W) * e1' * (g' : MulAut W)⁻¹ * e2' := by
      simp [hy]
    rw [hyW] at h16
    have hle := h16.trans hquad
    rw [hW20] at hcm
    have : Nat.card (fixV (Subgroup.zpowers (c' : MulAut W))) ≤ 2 ^ 15 := by
      by_contra hgt
      push Not at hgt
      have : 2 ^ 15 * 2 ^ 5 < Nat.card (fixV (Subgroup.zpowers (c' : MulAut W))) *
          (fixV (Subgroup.zpowers (c' : MulAut W))).index :=
        Nat.mul_lt_mul_of_lt_of_le hgt hc5 (lt_of_lt_of_le (by norm_num) hc5)
      omega
    omega

end CFSG.Quasithin.B45Exc
