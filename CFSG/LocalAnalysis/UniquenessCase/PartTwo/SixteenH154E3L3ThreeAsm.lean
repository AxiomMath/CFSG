module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Mult
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Fin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_finite_mulAut (W : Type) [Group W] [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_e3_centerless_elem {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hL : IsL3 ↥L 1) : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1 := by
  intro a ha hc
  have h1 := s16h_isL3_centreless hL ⟨a, ha⟩ fun b => Subtype.ext (hc b b.2)
  exact congrArg Subtype.val h1

private theorem s16h_e3_commSub_map_le {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {g : MulAut W} (hg : ∀ x ∈ L, g * x * g⁻¹ ∈ L) :
    (commSub ⊤ L).map g.toMonoidHom ≤ commSub ⊤ L := by
  unfold commSub
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨c, ⟨x, hx, w, -, rfl⟩, rfl⟩
  refine Subgroup.subset_closure ⟨g * x * g⁻¹, hg x hx, g w, Subgroup.mem_top _, ?_⟩
  simp [MulAut.mul_apply, map_mul, map_inv]

private theorem s16h_e3_pow_three_nine_le {n : ℕ} (h : 3 < 3 ^ n) : 9 ≤ 3 ^ n := by
  have hn : 2 ≤ n := by
    by_contra hlt
    have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with h0 | h1
    · rw [h0, pow_zero] at h; omega
    · rw [h1, pow_one] at h; omega
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem s16h_e3_lift_three {K A : Type} [Group K] [Finite K] [Group A] (π : K →* A)
    (hker : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1) {h : A} (hh : h ∈ π.range) (h3 : h ^ 3 = 1) :
    ∃ k : K, π k = h ∧ k ^ 3 = 1 := by
  by_cases h1 : h = 1
  · exact ⟨1, by simp [h1]⟩
  · obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hh
    have hh3 : orderOf h = 3 := by
      have hdvd : orderOf h ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hh1 | hh1
      · exact absurd (orderOf_eq_one_iff.mp hh1) h1
      · exact hh1
    have h3g : 3 ∣ orderOf g := by
      have hdvd := orderOf_map_dvd π g
      rw [hg, hh3] at hdvd
      exact hdvd
    let m : ℕ := orderOf g / 3
    have hm3 : m * 3 = orderOf g := Nat.div_mul_cancel h3g
    have hgm3 : (g ^ m) ^ 3 = 1 := by
      rw [← pow_mul, hm3, pow_orderOf_eq_one]
    have hgm_ne : g ^ m ≠ 1 := by
      intro hgm1
      have hdvd : orderOf g ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hgm1
      have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) h3g) (by norm_num)
      have hle : orderOf g ≤ m := Nat.le_of_dvd hmpos hdvd
      rw [← hm3] at hle
      omega
    have hhm_ne : h ^ m ≠ 1 := by
      intro hhm1
      have hgm_ker : g ^ m ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_pow, hg, hhm1]
      exact hgm_ne (hker (g ^ m) hgm_ker hgm3)
    have hmmod : m % 3 = 1 ∨ m % 3 = 2 := by
      have hlt : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hne : m % 3 ≠ 0 := by
        intro h0
        apply hhm_ne
        rw [← pow_mod_orderOf, hh3, h0, pow_zero]
      omega
    rcases hmmod with hm1 | hm2
    · refine ⟨g ^ m, ?_, hgm3⟩
      rw [map_pow, hg, ← pow_mod_orderOf, hh3, hm1, pow_one]
    · refine ⟨(g ^ m)⁻¹, ?_, ?_⟩
      · rw [map_inv, map_pow, hg, ← pow_mod_orderOf, hh3, hm2]
        have hh2h : h ^ 2 * h = 1 := by
          rw [← pow_succ]
          simpa using h3
        exact inv_eq_of_mul_eq_one_right hh2h
      · rw [inv_pow, hgm3, inv_one]

theorem s16h_e3_l3_three_asm {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsL3 ↥L 1)
    (hsum : SumOfNat (fun H V Z => BinaryNaturalSL H V Z 3 1) L U ⊥ 3)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ X ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom)
    (hrank : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian 3 E → Nat.card ↥E ≤ 27)
    (hrk3 : ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 27) :
    ∀ w ∈ U, w ≠ 1 → ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E ∧
      ∀ e ∈ E, e w = w := by
  intro w hwU hw1
  classical
  haveI : Finite (MulAut W) := s16h_e3_finite_mulAut W
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hno
  have hbadw : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian 3 E →
      (∀ e ∈ E, e w = w) → Nat.card ↥E ≤ 3 := by
    intro E hEX hEab hEfix
    by_contra hle
    have h3 : 3 < Nat.card ↥E := not_le.mp hle
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hEab.isPGroup
    have h9 : 9 ≤ Nat.card ↥E := by
      rw [hj] at h3 ⊢
      exact s16h_e3_pow_three_nine_le h3
    exact hno ⟨E, hEX, hEab, h9, hEfix⟩
  have hcen : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1 := s16h_e3_centerless_elem hL
  have hpL : 3 ∣ Nat.card ↥L := by rw [card_eq_of_isL3 hL]; norm_num
  have hAut : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥L) := fun h9 =>
    absurd (h9.trans (card_mulAut_dvd_of_isL3 hL)) (by decide)
  have hrk : ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 3 := by
    obtain ⟨E, h1, h2, h3⟩ := hrk3
    exact ⟨E, h1, h2, by rw [h3]; norm_num⟩
  obtain ⟨⟨d, hdK, hdord⟩, hnomove⟩ :=
    s16h_e3_frame_p F Nat.prime_three (by norm_num) hcen hpL hAut hrk hwU hbadw
  obtain ⟨t, -, hLt, -⟩ := F.swap
  have hLe : ↥L ≃* ↥L' :=
    (L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      (MulEquiv.subgroupCongr hLt)
  have hL' : IsL3 ↥L' 1 := CFSG.Blueprint.LieModel.of_mulEquiv hLe hL
  have hcen' : ∀ a ∈ L', (∀ b ∈ L', a * b = b * a) → a = 1 := s16h_e3_centerless_elem hL'
  obtain ⟨C⟩ := s16h_e3_l3_coord (W := W)
    (Y := X ⊓ normalizer (L : Set (MulAut W))) hL F.u_eq hsum inf_le_right htrans
  obtain ⟨π, hπ, hπ7⟩ := s16h_e3_l3_mult F hL C htrans
  let K : Subgroup (MulAut W) :=
    X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))
  have hdK' : d ∈ K := hdK
  have hdcent : d ∈ Subgroup.centralizer
      ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) := (Subgroup.mem_inf.mp hdK).2
  let dK : ↥K := ⟨d, hdK'⟩
  have hd3 : d ^ 3 = 1 := by
    have h := pow_orderOf_eq_one d
    rwa [hdord] at h
  have hdne : d ≠ 1 := by
    intro hd1
    rw [hd1, orderOf_one] at hdord
    omega
  have hpi_ne : π dK ≠ 1 := by
    intro hpi1
    obtain ⟨⟨u, hu, hdu⟩, -⟩ := hnomove d hdK hd3 hdne
    have hduU : d u ∈ U := by
      rw [F.u_eq]
      refine s16h_e3_commSub_map_le (L := L) (g := d) ?_
        (Subgroup.mem_map_of_mem d.toMonoidHom (F.u_eq ▸ hu))
      intro y hy
      have hcy : d * y = y * d :=
        (Subgroup.mem_centralizer_iff.mp hdcent y (Subgroup.mem_sup_left hy)).symm
      have hEq : d * y * d⁻¹ = y := by rw [hcy, mul_assoc, mul_inv_cancel, mul_one]
      rw [hEq]; exact hy
    have h1 := hπ dK u hu hduU
    rw [hpi1] at h1
    simp at h1
    exact hdu (by simpa using h1)
  have hdKpow : dK ^ 3 = 1 := by
    have hdiv : orderOf dK ∣ 3 := by rw [Subgroup.orderOf_mk, hdord]
    exact orderOf_dvd_iff_pow_eq_one.mp hdiv
  have hpid3 : (π dK) ^ 3 = 1 := by
    rw [← map_pow, hdKpow, map_one]
  have horder_pid : orderOf (π dK) = 3 := by
    have hdvd : orderOf (π dK) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hpid3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hpi_ne
    · exact h
  have h3dvd : 3 ∣ Nat.card ↥π.range := by
    have hmem : π dK ∈ π.range := MonoidHom.mem_range.mpr ⟨dK, rfl⟩
    have h := π.range.orderOf_dvd_natCard hmem
    rwa [horder_pid] at h
  have h21 : 21 ∣ Nat.card ↥π.range := by
    rw [show 21 = 3 * 7 by norm_num]
    exact (by norm_num : Nat.Coprime 3 7).mul_dvd_of_dvd_of_dvd h3dvd hπ7
  have hker : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1 := by
    intro x hxker hx3
    by_contra hxne
    have hxne' : (x : MulAut W) ≠ 1 := fun h => hxne (Subtype.ext h)
    have hx3' : (x : MulAut W) ^ 3 = 1 := by
      have h := congrArg (fun y : ↥K => (y : MulAut W)) hx3
      simpa using h
    obtain ⟨⟨u, hu, hxu⟩, -⟩ := hnomove (x : MulAut W) x.2 hx3' hxne'
    have hxker' : π x = 1 := MonoidHom.mem_ker.mp hxker
    have hxcent : (x : MulAut W) ∈ Subgroup.centralizer
        ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) := (Subgroup.mem_inf.mp x.2).2
    have huU : (x : MulAut W) u ∈ U := by
      rw [F.u_eq]
      refine s16h_e3_commSub_map_le (L := L) (g := (x : MulAut W)) ?_
        (Subgroup.mem_map_of_mem (x : MulAut W).toMonoidHom (F.u_eq ▸ hu))
      intro y hy
      have hcy : (x : MulAut W) * y = y * (x : MulAut W) :=
        (Subgroup.mem_centralizer_iff.mp hxcent y (Subgroup.mem_sup_left hy)).symm
      have hEq : (x : MulAut W) * y * (x : MulAut W)⁻¹ = y := by
        rw [hcy, mul_assoc, mul_inv_cancel, mul_one]
      rw [hEq]; exact hy
    have h1 := hπ x u hu huU
    rw [hxker'] at h1
    simp at h1
    exact hxu (by simpa using h1)
  set M : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    Multiplicative.toAdd (C.ψ ⟨w, hwU⟩) with hMdef
  have hM : M ≠ 0 := by
    intro hM0
    apply hw1
    have hψw1 : C.ψ ⟨w, hwU⟩ = 1 := by
      have h : Multiplicative.ofAdd M = (1 : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
        rw [ofAdd_eq_one]
        exact hM0
      simpa [hMdef, ofAdd_toAdd] using h
    have hsub : (⟨w, hwU⟩ : ↥U) = 1 := C.ψ.injective (by rw [hψw1, map_one])
    exact congrArg Subtype.val hsub
  obtain ⟨um, hm, hhmH, hum3, hhm3, hpne, hfix⟩ :=
    s16h_e3_l3_cover_three (H := π.range) h21 M hM
  obtain ⟨k, hkπ, hk3⟩ := s16h_e3_lift_three π hker hhmH hhm3
  have hkcent : (k : MulAut W) ∈ Subgroup.centralizer
      ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) := (Subgroup.mem_inf.mp k.2).2
  let l : ↥L := C.ρ.symm um
  let lW : MulAut W := l
  have hlL : lW ∈ L := l.2
  let x : MulAut W := lW * (k : MulAut W)
  have hcomm_lk : Commute lW (k : MulAut W) :=
    Subgroup.mem_centralizer_iff.mp hkcent lW (Subgroup.mem_sup_left hlL)
  have hlwU : lW w ∈ U := by
    rw [F.u_eq]
    exact s16h_e3_commSub_map_le (L := L) (g := lW)
      (fun y hy => L.mul_mem (L.mul_mem hlL hy) (L.inv_mem hlL))
      (Subgroup.mem_map_of_mem lW.toMonoidHom (F.u_eq ▸ hwU))
  have hψlw : C.ψ ⟨lW w, hlwU⟩ = Multiplicative.ofAdd (um * M) := by
    have h := C.equivariant l w hwU hlwU
    rw [show C.ρ l = um by simp [l], ← hMdef] at h
    exact h
  have hl3 : lW ^ 3 = 1 := by
    have h : (C.ρ.symm um) ^ 3 = 1 := by rw [← map_pow, hum3, map_one]
    have h2 := congrArg (fun y : ↥L => (y : MulAut W)) h
    simpa [lW, l] using h2
  have hk3W : (k : MulAut W) ^ 3 = 1 := by
    have h := congrArg (fun y : ↥K => (y : MulAut W)) hk3
    simpa using h
  have hx3 : x ^ 3 = 1 := by
    show (lW * (k : MulAut W)) ^ 3 = 1
    rw [hcomm_lk.mul_pow 3, hl3, hk3W, mul_one]
  have hkWlw : (k : MulAut W) (lW w) = w := by
    have htoAdd : Multiplicative.toAdd (C.ψ ⟨lW w, hlwU⟩) = um * M := by
      rw [hψlw, toAdd_ofAdd]
    have hklwU : (k : MulAut W) (lW w) ∈ U := by
      rw [F.u_eq]
      refine s16h_e3_commSub_map_le (L := L) (g := (k : MulAut W)) ?_
        (Subgroup.mem_map_of_mem (k : MulAut W).toMonoidHom (F.u_eq ▸ hlwU))
      intro y hy
      have hcy : (k : MulAut W) * y = y * (k : MulAut W) :=
        (Subgroup.mem_centralizer_iff.mp hkcent y (Subgroup.mem_sup_left hy)).symm
      have hEq : (k : MulAut W) * y * (k : MulAut W)⁻¹ = y := by
        rw [hcy, mul_assoc, mul_inv_cancel, mul_one]
      rw [hEq]; exact hy
    have h1 := hπ k (lW w) hlwU hklwU
    rw [htoAdd, hkπ, hfix] at h1
    have h2 : C.ψ ⟨(k : MulAut W) (lW w), hklwU⟩ = C.ψ ⟨w, hwU⟩ := by
      rw [h1, hMdef, ofAdd_toAdd]
    exact congrArg Subtype.val (C.ψ.injective h2)
  have hxw : x w = w := by
    show (lW * (k : MulAut W)) w = w
    have happly : lW ((k : MulAut W) w) = (k : MulAut W) (lW w) := by
      simpa using congrArg (fun f : MulAut W => f w) hcomm_lk.eq
    rw [MulAut.mul_apply, happly, hkWlw]
  have hxne : x ≠ 1 := by
    intro hx1
    have hmul : lW * (k : MulAut W) = 1 := by simpa [x] using hx1
    have hl_eq : lW = (k : MulAut W)⁻¹ := eq_inv_of_mul_eq_one_left hmul
    have hl_cent : ∀ b ∈ L, lW * b = b * lW := by
      intro b hb
      have hkb : Commute (k : MulAut W) b :=
        (Subgroup.mem_centralizer_iff.mp hkcent b (Subgroup.mem_sup_left hb)).symm
      have hkinvb : (k : MulAut W)⁻¹ * b = b * (k : MulAut W)⁻¹ := hkb.inv_left.eq
      rw [hl_eq]
      exact hkinvb
    have hl1 : lW = 1 := hcen lW hlL hl_cent
    have hk1 : (k : MulAut W) = 1 := by
      rw [hl1, one_mul] at hmul
      exact hmul
    have hhm1 : hm = 1 := by rw [← hkπ, show k = 1 from Subtype.ext hk1, map_one]
    have hum1 : um = 1 := by
      have hl1' : l = 1 := Subtype.ext hl1
      have h : C.ρ l = C.ρ 1 := by rw [hl1']
      simpa [l] using h
    rcases hpne with hum | hhm
    · exact hum hum1
    · exact hhm hhm1
  have hxX : x ∈ X := by
    show lW * (k : MulAut W) ∈ X
    exact X.mul_mem (F.le_x hlL) (Subgroup.mem_inf.mp k.2).1
  have hxcommL' : ∀ b ∈ L', x * b = b * x := by
    intro b hb
    have h1 : Commute lW b := F.comm lW hlL b hb
    have h2 : Commute (k : MulAut W) b :=
      (Subgroup.mem_centralizer_iff.mp hkcent b (Subgroup.mem_sup_right hb)).symm
    show (lW * (k : MulAut W)) * b = b * (lW * (k : MulAut W))
    exact (h1.mul_left h2).eq
  have hx_not_L' : x ∉ L' := by
    intro hxL'
    exact hxne (hcen' x hxL' hxcommL')
  have hcardL' : 3 ∣ Nat.card ↥L' := by
    rw [← Nat.card_congr hLe.toEquiv, card_eq_of_isL3 hL]
    norm_num
  obtain ⟨y', hy'ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥L') 3 hcardL'
  let yW : MulAut W := y'
  have hyWL' : yW ∈ L' := y'.2
  have hyW3 : yW ^ 3 = 1 := by
    have h : y' ^ 3 = 1 := by
      have h := pow_orderOf_eq_one y'
      rwa [hy'ord] at h
    have h2 := congrArg (fun z : ↥L' => (z : MulAut W)) h
    simpa [yW] using h2
  have hcommxy : Commute x yW := hxcommL' yW hyWL'
  have hx_not_zy : x ∉ Subgroup.zpowers yW := by
    intro hxmem
    exact hx_not_L' ((Subgroup.zpowers_le.mpr hyWL') hxmem)
  let E : Subgroup (MulAut W) := Subgroup.zpowers x ⊔ Subgroup.zpowers yW
  have hEX : E ≤ X := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr hxX
    · exact Subgroup.zpowers_le.mpr (F.le_x' hyWL')
  have hEab : IsElemAbelian 3 E := by
    apply IsElemAbelian.sup_of_commute
    · exact isElemAbelian_zpowers hx3
    · exact isElemAbelian_zpowers hyW3
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (hcommxy.zpow_zpow i j).eq
  have hEfix : ∀ e ∈ E, e w = w := by
    have hle : E ≤ MulAction.stabilizer (MulAut W) w := by
      apply sup_le
      · rw [Subgroup.zpowers_le]
        exact MulAction.mem_stabilizer_iff.mpr hxw
      · rw [Subgroup.zpowers_le]
        exact MulAction.mem_stabilizer_iff.mpr (by simpa using F.fix_u yW hyWL' w hwU)
    intro e he
    exact MulAction.mem_stabilizer_iff.mp (hle he)
  have hcard9 : 9 ≤ Nat.card ↥E := by
    have h3lt : 3 < Nat.card ↥E := by
      by_contra hle
      have h3le : Nat.card ↥E ≤ 3 := not_lt.mp hle
      have hcardzy : Nat.card ↥(Subgroup.zpowers yW) = 3 := by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy'ord]
      have hEq : Subgroup.zpowers yW = E :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcardzy]; exact h3le)
      exact hx_not_zy (hEq.ge (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hEab.isPGroup
    have h3lt' : 3 < 3 ^ j := by rwa [hj] at h3lt
    have h9 := s16h_e3_pow_three_nine_le h3lt'
    rwa [← hj] at h9
  exact hno ⟨E, hEX, hEab, hcard9, hEfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
