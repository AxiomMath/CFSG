module

public import CFSG.RankThree.PartOne.Q1327T.GlueWeyl
public import CFSG.RankThree.PartOne.S12.Sec154
public import CFSG.RankThree.PartOne.Q1327.Irr

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327 CFSG.RankThree.PartOne.Torsion37
open scoped Pointwise

variable {G : Type} [Group G] {p : ℕ} {E : Subgroup G}

theorem smul_zpowers_apply (g : MulAut E) (a : E) :
    g • Subgroup.zpowers a = Subgroup.zpowers (g a) := by
  ext y
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [MulAut.smul_def, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ n
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨a ^ n, Subgroup.zpow_mem_zpowers a n, by rw [MulAut.smul_def, map_zpow]⟩

theorem smul_zpowers_eq_of_mem [Finite G] (g : MulAut E) (a : E) (h : g a ∈ Subgroup.zpowers a) :
    g • Subgroup.zpowers a = Subgroup.zpowers a := by
  have hle : g • Subgroup.zpowers a ≤ Subgroup.zpowers a := by
    rw [smul_zpowers_apply, Subgroup.zpowers_le]
    exact h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [smul_zpowers_apply, Nat.card_zpowers, Nat.card_zpowers, MulEquiv.orderOf_eq]

theorem three_le_card_orbit_zpowers [Finite G] (hd : RefFacts.ElemData p E)
    (hcard : Nat.card E = p ^ 3) {W : Subgroup (MulAut E)}
    (hirr : ∀ B : Subgroup E, (∀ g ∈ W, ∀ b ∈ B, g b ∈ B) → B = ⊥ ∨ B = ⊤) {a : E}
    (ha1 : a ≠ 1) : 3 ≤ Nat.card (MulAction.orbit W (Subgroup.zpowers a)) := by
  classical
  by_contra hlt
  push Not at hlt
  set O := MulAction.orbit W (Subgroup.zpowers a) with hO
  have haO : Subgroup.zpowers a ∈ O := MulAction.mem_orbit_self _
  have hfin : O.Finite := Set.toFinite O
  have hncard : O.ncard ≤ 2 := by
    rw [← Nat.card_coe_set_eq]
    omega
  set B : Subgroup E := Subgroup.closure (MulAction.orbit W a) with hB
  have hBinv : ∀ g ∈ W, ∀ b ∈ B, g b ∈ B := by
    intro g hg b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨h, hh⟩, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨⟨g * h, Subgroup.mul_mem _ hg hh⟩, rfl⟩
    | one => rw [map_one]; exact B.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact B.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact B.inv_mem hx
  have hB1 : B ≠ ⊥ := fun h => ha1 (by
    have : a ∈ B := Subgroup.subset_closure (MulAction.mem_orbit_self a)
    rw [h] at this
    exact this)
  have hBtop : B = ⊤ := (hirr B hBinv).resolve_left hB1
  obtain ⟨y, hOy⟩ : ∃ y : E, O ⊆ {Subgroup.zpowers a, Subgroup.zpowers y} := by
    by_cases hex : ∃ b ∈ O, b ≠ Subgroup.zpowers a
    · obtain ⟨b, hbO, hba⟩ := hex
      obtain ⟨⟨g, hg⟩, hgb⟩ := hbO
      have hb : b = Subgroup.zpowers ((g : MulAut E) a) := by
        rw [← hgb]
        exact smul_zpowers_apply g a
      refine ⟨(g : MulAut E) a, fun c hc => ?_⟩
      by_contra hcn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcn
      have : 2 < O.ncard := (Set.two_lt_ncard_iff hfin).2
        ⟨Subgroup.zpowers a, b, c, haO, ⟨⟨g, hg⟩, hgb⟩, hc, hba.symm,
          fun h => hcn.1 h.symm, fun h => hcn.2 (hb ▸ h.symm)⟩
      omega
    · push Not at hex
      exact ⟨a, fun c hc => by simp [hex c hc]⟩
  have hBle : B ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers y := by
    rw [hB, Subgroup.closure_le]
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hmem : (g : MulAut E) • Subgroup.zpowers a ∈ O := ⟨⟨g, hg⟩, rfl⟩
    have hga : ((g : MulAut E) a : E) ∈ (g : MulAut E) • Subgroup.zpowers a := by
      rw [smul_zpowers_apply]
      exact Subgroup.mem_zpowers _
    rcases hOy hmem with h | h
    · rw [h] at hga
      exact Subgroup.mem_sup_left hga
    · rw [h] at hga
      exact Subgroup.mem_sup_right hga
  have h1 := Subgroup.card_le_of_le hBle
  have h2 := card_sup_zpowers_le hd a y
  rw [hBtop, Subgroup.card_top, hcard] at h1
  have hp2 := hd.prime.two_le
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hd.prime.one_lt (by norm_num)
  omega

theorem three_mul_card_le [Finite G] (hd : RefFacts.ElemData p E) (hcard : Nat.card E = p ^ 3)
    {W Z W₀ N : Subgroup (MulAut E)}
    (hirr : ∀ B : Subgroup E, (∀ g ∈ W, ∀ b ∈ B, g b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hZW : Z ≤ W) (hZ : ∀ z ∈ Z, ∃ k : ℤ, ∀ e : E, z e = e ^ k)
    (hsurj : ∀ g ∈ W, ∃ z ∈ Z, ∃ w ∈ W₀, g = z * w)
    (hNW : N ≤ W) {a : E} (ha1 : a ≠ 1) (hNa : ∀ g ∈ N, g a = a) :
    3 * Nat.card N ≤ Nat.card W₀ := by
  classical
  have : Finite (MulAut E) :=
    Finite.of_injective (fun φ : MulAut E => (φ : E → E)) DFunLike.coe_injective
  have : Fact p.Prime := ⟨hd.prime⟩
  have hao : orderOf a = p := orderOf_eq_prime (hd.pow a) ha1
  have hpowk : ∀ k : ℤ, a ^ k = a → ∀ e : E, e ^ k = e := by
    intro k hk e
    have h1 : a ^ (k - 1) = 1 := by rw [zpow_sub, hk, zpow_one, mul_inv_cancel]
    have h2 : (p : ℤ) ∣ k - 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := a) (i := k - 1)).2 h1
      rwa [hao] at this
    obtain ⟨m, hm⟩ := h2
    have hk' : k = 1 + p * m := by linarith
    rw [hk', zpow_add, zpow_one, zpow_mul, zpow_natCast, hd.pow e, one_zpow, mul_one]
  have hZfix : ∀ g ∈ Z, g a = a → g = 1 := by
    intro g hg hga
    obtain ⟨k, hk⟩ := hZ g hg
    have hak : a ^ k = a := by rw [← hk a]; exact hga
    refine MulEquiv.ext fun e => ?_
    rw [hk e, hpowk k hak e]
    rfl
  have hZline : ∀ z ∈ Z, z • Subgroup.zpowers a = Subgroup.zpowers a := by
    intro z hz
    obtain ⟨k, hk⟩ := hZ z hz
    refine smul_zpowers_eq_of_mem z a ?_
    rw [hk a]
    exact Subgroup.zpow_mem_zpowers a k
  have hNline : ∀ n ∈ N, n • Subgroup.zpowers a = Subgroup.zpowers a := by
    intro n hn
    refine smul_zpowers_eq_of_mem n a ?_
    rw [hNa n hn]
    exact Subgroup.mem_zpowers a
  set L : Subgroup W := MulAction.stabilizer W (Subgroup.zpowers a) with hL
  let ι : ↥N × ↥Z → ↥L := fun x =>
    ⟨⟨(x.1 : MulAut E) * x.2, W.mul_mem (hNW x.1.2) (hZW x.2.2)⟩, by
      rw [hL, MulAction.mem_stabilizer_iff]
      show ((x.1 : MulAut E) * (x.2 : MulAut E)) • Subgroup.zpowers a = Subgroup.zpowers a
      rw [mul_smul, hZline _ x.2.2, hNline _ x.1.2]⟩
  have hι : Function.Injective ι := by
    rintro ⟨⟨n, hn⟩, ⟨z, hz⟩⟩ ⟨⟨n', hn'⟩, ⟨z', hz'⟩⟩ h
    have h1 : n * z = n' * z' := congrArg (fun x : ↥L => ((x : ↥W) : MulAut E)) h
    have h2 : n'⁻¹ * n = z' * z⁻¹ := by
      have : n'⁻¹ * (n * z) * z⁻¹ = n'⁻¹ * (n' * z') * z⁻¹ := by rw [h1]
      simpa [mul_assoc] using this
    have hz1 : z' * z⁻¹ ∈ Z := Z.mul_mem hz' (Z.inv_mem hz)
    have hn1 : n'⁻¹ * n ∈ N := N.mul_mem (N.inv_mem hn') hn
    have hfix : (z' * z⁻¹) a = a := by rw [← h2]; exact hNa _ hn1
    have h3 : z' * z⁻¹ = 1 := hZfix _ hz1 hfix
    have hzz : z' = z := mul_inv_eq_one.1 h3
    have hnn : n' = n := by
      rw [h3] at h2
      exact inv_mul_eq_one.1 h2
    subst hzz
    subst hnn
    rfl
  have h4 : Nat.card N * Nat.card Z ≤ Nat.card L := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective ι hι
  have h3 := three_le_card_orbit_zpowers hd hcard hirr ha1
  have hidx : L.index = Nat.card (MulAction.orbit W (Subgroup.zpowers a)) :=
    MulAction.index_stabilizer W _
  have hLW : Nat.card L * L.index = Nat.card W := Subgroup.card_mul_index L
  have h5 : Nat.card W ≤ Nat.card Z * Nat.card W₀ := by
    choose! zf hzf wf hwf hgeq using hsurj
    let ι2 : ↥W → ↥Z × ↥W₀ := fun g => (⟨zf g, hzf g g.2⟩, ⟨wf g, hwf g g.2⟩)
    have hι2 : Function.Injective ι2 := by
      intro g g' h
      have e1 : zf g = zf g' := congrArg (fun x : ↥Z × ↥W₀ => (x.1 : MulAut E)) h
      have e2 : wf g = wf g' := congrArg (fun x : ↥Z × ↥W₀ => (x.2 : MulAut E)) h
      exact Subtype.ext ((hgeq g g.2).trans ((by rw [e1, e2] : zf g * wf g = zf g' * wf g')
        |>.trans (hgeq g' g'.2).symm))
    have := Nat.card_le_card_of_injective ι2 hι2
    rwa [Nat.card_prod] at this
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have h6 : 3 * Nat.card N * Nat.card Z ≤ Nat.card W₀ * Nat.card Z := by
    calc 3 * Nat.card N * Nat.card Z = 3 * (Nat.card N * Nat.card Z) := by ring
      _ ≤ 3 * Nat.card L := Nat.mul_le_mul_left 3 h4
      _ ≤ Nat.card L * L.index := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (hidx ▸ h3)
      _ = Nat.card W := hLW
      _ ≤ Nat.card Z * Nat.card W₀ := h5
      _ = Nat.card W₀ * Nat.card Z := mul_comm _ _
  exact Nat.le_of_mul_le_mul_right h6 hZpos

section Structure

variable [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {f r : ℕ} {R : Subgroup G}
  {s s' zs : MulAut E}

theorem exists_weyl_structure (H : Hyp G p A c L E f r R s s' zs) :
    ∃ Z W₀ : Subgroup (MulAut E), Z ≤ torusWeyl E ∧ W₀ ≤ torusWeyl E ∧ Nat.card W₀ = 24 ∧
      Nonempty (W₀ ≃* Equiv.Perm (Fin 4)) ∧
      (∀ z ∈ Z, ∃ k : ℤ, ∀ e : E, z e = e ^ k) ∧
      (∀ z ∈ Z, ∀ g ∈ torusWeyl E, z * g = g * z) ∧
      (∀ g ∈ torusWeyl E, ∃ z ∈ Z, ∃ w ∈ W₀, g = z * w) := by
  classical
  obtain ⟨eX⟩ := H.hweyl
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Subgroup (MulAut E), Weyl154 p E W₀ := by
    obtain ⟨ψ, hψ, hψD⟩ := Sec154Fin.swapClass_gp (Sec154.classes_gp H.h12 H.hF13 H.hEA eX)
    exact Sec154.node154_core H.h12 H.hF13 eX Sec154Fin.pCore_gp ψ hψ hψD
  obtain ⟨-, hW₀X, hiso, hsup, -, hscal⟩ := hW₀
  have : Finite (MulAut E) :=
    Finite.of_injective (fun φ : MulAut E => (φ : E → E)) DFunLike.coe_injective
  have hW₀W : W₀ ≤ torusWeyl E := hW₀X.trans (Sec1322.reflectionGroup_le E)
  have h48 : Nat.card W₀ ≤ 48 :=
    (Subgroup.card_le_of_le hW₀X).trans (card_reflectionGroup_eq eX).le
  have h24 : Nat.card W₀ = 24 ∧ Nonempty (W₀ ≃* Equiv.Perm (Fin 4)) := by
    rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · refine ⟨?_, ⟨e⟩⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    · exfalso
      have h120 : Nat.card W₀ = 120 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
          Fintype.card_fin]
        rfl
      omega
  refine ⟨(Subgroup.center ↥(torusWeyl E)).map (torusWeyl E).subtype, W₀,
    Subgroup.map_subtype_le _, hW₀W, h24.1, h24.2, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hscal z hz
  · rintro _ ⟨z, hz, rfl⟩ g hg
    have := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
    exact (congrArg Subtype.val this).symm
  · intro g hg
    rw [hsup] at hg
    exact exists_mul_of_mem_sup_of_commute (fun k hk l hl => by
      obtain ⟨z, hz, rfl⟩ := hk
      have := Subgroup.mem_center_iff.1 hz ⟨l, hW₀W hl⟩
      exact (congrArg Subtype.val this).symm) hg

theorem irreducible_torusWeyl (hF13 : Sec13Facts G p A c L E) :
    ∀ B : Subgroup E, (∀ g ∈ torusWeyl E, ∀ b ∈ B, g b ∈ B) → B = ⊥ ∨ B = ⊤ := by
  intro B hB
  have hinv : torusInvariant E ⊤ (B.map E.subtype) := by
    intro w hw b hb
    have hwN : w ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.1 hw).2
    obtain ⟨b', hb', rfl⟩ := hb
    have hg : conjAut E w hwN ∈ torusWeyl E := ⟨⟨w, hwN⟩, rfl⟩
    exact ⟨conjAut E w hwN b', hB _ hg b' hb', Equivariance.coe_conjAut hwN b'⟩
  rcases hF13.irreducible _ (Subgroup.map_subtype_le B) hinv with h0 | h1
  · left
    rw [eq_bot_iff]
    intro b hb
    have : (b : G) ∈ B.map E.subtype := ⟨b, hb, rfl⟩
    rw [h0] at this
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 this))
  · right
    rw [eq_top_iff]
    intro e _
    have : (e : G) ∈ B.map E.subtype := by
      rw [h1]
      exact e.2
    obtain ⟨b, hb, hbe⟩ := this
    rwa [← Subtype.ext hbe]

theorem isSolvable_of_le_torusWeyl (H : Hyp G p A c L E f r R s s' zs)
    {Γ : Subgroup (MulAut E)} (hΓ : Γ ≤ torusWeyl E) : Group.IsSolvable ↥Γ := by
  obtain ⟨Z, W₀, hZW, hW₀W, -, ⟨e⟩, -, hcen, hdec⟩ := exists_weyl_structure H
  have hcomm : ∀ (m : ↥Z) (n : ↥W₀), Commute (Z.subtype m) (W₀.subtype n) := fun m n =>
    hcen m m.2 n (hW₀W n.2)
  let φ := MonoidHom.noncommCoprod Z.subtype W₀.subtype hcomm
  have hZs : Group.IsSolvable ↥Z :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hcen a a.2 b (hZW b.2))
  have hS4 : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  have hW₀s : Group.IsSolvable ↥W₀ :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hrs : Group.IsSolvable ↥φ.range := Group.isSolvable_of_surjective φ.rangeRestrict_surjective
  have hle : Γ ≤ φ.range := by
    intro g hg
    obtain ⟨z, hz, w, hw, rfl⟩ := hdec g (hΓ hg)
    exact ⟨(⟨z, hz⟩, ⟨w, hw⟩), by simp [φ]⟩
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem card_eq_six_of_fixes (H : Hyp G p A c L E f r R s s' zs)
    {N : Subgroup (MulAut E)} (hNW : N ≤ torusWeyl E) {a : E} (ha1 : a ≠ 1)
    (hNa : ∀ g ∈ N, g a = a) {ρ σ : MulAut E} (hρ : ρ ∈ N) (hσ : σ ∈ N) (hρo : orderOf ρ = 3)
    (hσo : orderOf σ = 2) : Nat.card N = 6 := by
  have h := H.h12
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := Sec12Three.five_le h; omega
  have hcard : Nat.card E = p ^ 3 := by rw [H.hEA]; exact h.A_card
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.E_elem
  obtain ⟨Z, W₀, hZW, hW₀W, hc24, -, hZ, -, hdec⟩ := exists_weyl_structure H
  have hle := three_mul_card_le hd hcard (irreducible_torusWeyl H.hF13) hZW hZ hdec hNW ha1 hNa
  have h4 : 3 ∣ Nat.card N := hρo ▸ Subgroup.orderOf_dvd_natCard N hρ
  have h5 : 2 ∣ Nat.card N := hσo ▸ Subgroup.orderOf_dvd_natCard N hσ
  have h6 : 6 ∣ Nat.card N := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 2) h4 h5
  have hpos : 0 < Nat.card N := Nat.card_pos
  omega

end Structure

end CFSG.RankThree.PartOne.Q1327T
