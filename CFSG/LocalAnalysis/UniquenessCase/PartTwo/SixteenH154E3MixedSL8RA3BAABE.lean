module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABEA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_kbar_central_element
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    ∃ κ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian),
      κ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧
      κ ∈ Subgroup.centralizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) ∧
      κ ∈ Subgroup.centralizer
        ((barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) : Subgroup _) : Set _) ∧
      orderOf κ = 7 ∧ κ ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  obtain ⟨d, hdk, hdord, hdn⟩ :=
    s16h_sl28_seven_kbar_element D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 h7
  let Vt := Vtil ⊥ V h.hyp151.isElemAbelian
  let Mb := Mbar D.M ⊥ V h.hyp151.isElemAbelian
  let Lb := lBar ⊥ V h.hyp151.isElemAbelian L
  let B := barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)
  let Wt := commSub ⊤ Lb
  have hdM : d ∈ Mb := hdk.1
  have hdcentL : d ∈ Subgroup.centralizer ((Lb : Subgroup _) : Set _) := hdk.2
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hx' : x ∈ stabTil ⊥ V := hMs hxM
  obtain ⟨m, hmM, hmd⟩ := (mem_barSub ⊥ V h.hyp151.isElemAbelian D.M d).1 hdM
  have hm'_stab : (m : G)⁻¹ ∈ stabTil ⊥ V := (stabTil ⊥ V).inv_mem m.2
  have hu : actTil ⊥ V h.hyp151.isElemAbelian ⟨(m : G)⁻¹, hm'_stab⟩ =
      (actTil ⊥ V h.hyp151.isElemAbelian m)⁻¹ := by
    rw [show (⟨(m : G)⁻¹, hm'_stab⟩ : stabTil ⊥ V) = m⁻¹ from Subtype.ext rfl, map_inv]
  have hconj : MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian
        ⟨(m : G)⁻¹, hm'_stab⟩)⁻¹ = MulAut.conj d := by
    rw [hu, hmd, inv_inv]
  have hform := s15_Infra_barSub_conjSubgroup (V₀ := ⊥) (V := V)
    h.hyp151.isElemAbelian hm'_stab (conjSubgroup L x)
  have hBmap : B.map (MulAut.conj d).toMonoidHom =
      barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L (x * (m : G)⁻¹)) := by
    have h1 : B.map (MulAut.conj d).toMonoidHom =
        B.map (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian
          ⟨(m : G)⁻¹, hm'_stab⟩)⁻¹).toMonoidHom := by rw [hconj]
    rw [h1, ← hform]
    exact congrArg (barSub ⊥ V h.hyp151.isElemAbelian)
      (conjSubgroup_conjSubgroup L x (m : G)⁻¹)
  have hmxM : x * (m : G)⁻¹ ∈ D.M := D.M.mul_mem hxM (D.M.inv_mem hmM)
  have hneB : B ≠ Lb := by
    intro hEq
    exact hxn ((s15_Infra_mem_nBar_iff h.hyp151.hyp125 h.hyp151.isElemAbelian hxM).2 hEq)
  have hdec : B.map (MulAut.conj d).toMonoidHom = B := by
    rcases c23_barSub_conj_cases D h.hyp151 h.hyp151.isElemAbelian hs2 hxM hxn
      (m := x * (m : G)⁻¹) hmxM with hcase | hcase
    · exfalso
      have hBd : B.map (MulAut.conj d).toMonoidHom = Lb := hBmap.trans hcase
      have hdconjL : Lb.map (MulAut.conj d⁻¹).toMonoidHom = Lb := by
        apply le_antisymm
        · intro z hz
          obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
          have hcomm : l * d = d * l := (Subgroup.mem_centralizer_iff.mp hdcentL) l hl
          have hfix : d⁻¹ * l * d = l := by
            calc d⁻¹ * l * d = d⁻¹ * (l * d) := by group
              _ = d⁻¹ * (d * l) := by rw [hcomm]
              _ = l := by group
          simpa [MulAut.conj_apply, hfix] using hl
        · intro l hl
          refine Subgroup.mem_map.mpr ⟨l, hl, ?_⟩
          have hcomm : l * d = d * l := (Subgroup.mem_centralizer_iff.mp hdcentL) l hl
          have hfix : d⁻¹ * l * d = l := by
            calc d⁻¹ * l * d = d⁻¹ * (l * d) := by group
              _ = d⁻¹ * (d * l) := by rw [hcomm]
              _ = l := by group
          simp [MulAut.conj_apply, hfix]
      have hcomp : (B.map (MulAut.conj d).toMonoidHom).map
          (MulAut.conj d⁻¹).toMonoidHom = B := by
        rw [Subgroup.map_map]
        have hid : (MulAut.conj d⁻¹).toMonoidHom.comp (MulAut.conj d).toMonoidHom =
            MonoidHom.id (MulAut Vt) := by
          ext y x
          simp [MulAut.conj_apply]
          rfl
        rw [hid, Subgroup.map_id]
      rw [hBd, hdconjL] at hcomp
      exact hneB hcomp.symm
    · exact hBmap.trans hcase
  let u : MulAut Vt := actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hx'⟩
  have hBformula : B = Lb.map (MulAut.conj u⁻¹).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup (V₀ := ⊥) (V := V) h.hyp151.isElemAbelian hx' L
  let eB : ↥Lb ≃* ↥B :=
    (MulEquiv.subgroupMap (MulAut.conj u⁻¹) Lb).trans
      (MulEquiv.subgroupCongr hBformula.symm)
  have hBsl : IsSLn ↥B 2 3 := IsSLn.of_mulEquiv eB hrow.1
  let cd : MulAut (MulAut Vt) := MulAut.conj d
  have hdB : B.map (cd : MulAut Vt →* MulAut Vt) = B := hdec
  let α : MulAut ↥B := (MulEquiv.subgroupMap cd B).trans (MulEquiv.subgroupCongr hdB)
  have hαcoe : ∀ y : ↥B, ((α y : ↥B) : MulAut Vt) = cd (y : MulAut Vt) := by
    intro y
    rfl
  have hd7 : d ^ 7 = 1 := by
    rw [← hdord]
    exact pow_orderOf_eq_one d
  have hcd7 : cd ^ 7 = 1 := by
    change (MulAut.conj d) ^ 7 = 1
    rw [← map_pow, hd7, map_one]
  have hαpow : ∀ n : ℕ, ∀ y : ↥B,
      (((α ^ n) y : ↥B) : MulAut Vt) = (cd ^ n) (y : MulAut Vt) := by
    intro n
    induction n with
    | zero =>
        intro y
        simp
    | succ n ih =>
        intro y
        calc (((α ^ (n + 1)) y : ↥B) : MulAut Vt)
            = ((α ((α ^ n) y) : ↥B) : MulAut Vt) := by rw [pow_succ']; rfl
          _ = cd (((α ^ n) y : ↥B) : MulAut Vt) := hαcoe _
          _ = cd ((cd ^ n) (y : MulAut Vt)) := by rw [ih y]
          _ = (cd ^ (n + 1)) (y : MulAut Vt) := by rw [pow_succ']; rfl
  have hα7 : α ^ 7 = 1 := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [hαpow 7 y, hcd7]
    rfl
  obtain ⟨β, hβ⟩ := s16h_sl28_aut_seven_inner hBsl α hα7
  have hβconj : ∀ y : ↥B,
      MulAut.conj d (y : MulAut Vt) = MulAut.conj (β : MulAut Vt) (y : MulAut Vt) := by
    intro y
    have h1 := congrArg (fun φ : MulAut ↥B => φ y) hβ
    have h2 : ((α y : ↥B) : MulAut Vt) = ((MulAut.conj β y : ↥B) : MulAut Vt) :=
      congrArg Subtype.val h1
    rw [hαcoe y] at h2
    simpa [cd, MulAut.conj_apply] using h2
  have hdβ : MulAut.conj d (β : MulAut Vt) = (β : MulAut Vt) := by
    simpa [MulAut.conj_apply, mul_assoc] using hβconj β
  have hdβ' : d * (β : MulAut Vt) * d⁻¹ = (β : MulAut Vt) := by
    simpa [MulAut.conj_apply] using hdβ
  have hdβcomm : d * (β : MulAut Vt) = (β : MulAut Vt) * d := by
    calc d * (β : MulAut Vt) = (d * (β : MulAut Vt) * d⁻¹) * d := by group
      _ = (β : MulAut Vt) * d := by rw [hdβ']
  have hβ7 : (β : MulAut Vt) ^ 7 = 1 := by
    have hβ7mem : β ^ 7 ∈ Subgroup.center ↥B := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hconj : MulAut.conj ((β : ↥B) ^ 7) = 1 := by
        rw [map_pow, ← hβ, hα7]
      have hy : MulAut.conj ((β : ↥B) ^ 7) y = y := by rw [hconj]; rfl
      rw [MulAut.conj_apply] at hy
      calc y * β ^ 7 = ((β : ↥B) ^ 7 * y * ((β : ↥B) ^ 7)⁻¹) * β ^ 7 := by rw [hy]
        _ = β ^ 7 * y := by group
    have hβ7sub : β ^ 7 = 1 := by
      have hmem := hβ7mem
      rw [s16h_sl28_center_eq_bot_of_isSLn_two (by norm_num) hBsl] at hmem
      exact Subgroup.mem_bot.mp hmem
    simpa using congrArg Subtype.val hβ7sub
  have hcommPair := h.hyp151.commute x hxM hxn
  have hLbB : Lb ≤ Subgroup.centralizer ((B : Subgroup _) : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp hcommPair.1
  have hβcentL : (β : MulAut Vt) ∈ Subgroup.centralizer ((Lb : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.mp (hLbB hl)) β β.2).symm
  have hBfixWt : B ≤ centSub Wt := by
    intro b hb
    rw [mem_centSub]
    intro w hw
    have hle : Wt ≤ fixV B := by
      apply commSub_eq_bot_iff.mp
      simpa [Wt, B, Lb, wTil, lBar] using hcommPair.2
    exact (mem_fixV.mp (hle hw)) b hb
  have hβfixWt : ∀ w ∈ Wt, (β : MulAut Vt) w = w := fun w hw => hBfixWt β.2 w hw
  let κ : MulAut Vt := (β : MulAut Vt)⁻¹ * d
  have hκM : κ ∈ Mb := by
    have hBM : B ≤ Mb := c23_barSub_conjSubgroup_le_Mbar D h.hyp151 h.hyp151.isElemAbelian hxM
    exact Mb.mul_mem (Mb.inv_mem (hBM β.2)) hdM
  have hκcentL : κ ∈ Subgroup.centralizer ((Lb : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hld : l * d = d * l := (Subgroup.mem_centralizer_iff.mp hdcentL) l hl
    have hlβ : l * (β : MulAut Vt) = (β : MulAut Vt) * l :=
      (Subgroup.mem_centralizer_iff.mp hβcentL) l hl
    have hlβinv : l * (β : MulAut Vt)⁻¹ = (β : MulAut Vt)⁻¹ * l := by
      have hcomm : Commute (β : MulAut Vt) l :=
        ((Subgroup.mem_centralizer_iff.mp hβcentL) l hl).symm
      exact (hcomm.inv_left).eq.symm
    dsimp [κ]
    calc l * ((β : MulAut Vt)⁻¹ * d) = (l * (β : MulAut Vt)⁻¹) * d := by group
      _ = ((β : MulAut Vt)⁻¹ * l) * d := by rw [hlβinv]
      _ = (β : MulAut Vt)⁻¹ * (l * d) := by group
      _ = (β : MulAut Vt)⁻¹ * (d * l) := by rw [hld]
      _ = ((β : MulAut Vt)⁻¹ * d) * l := by group
  have hκcentB : κ ∈ Subgroup.centralizer ((B : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hdy : d * y * d⁻¹ = (β : MulAut Vt) * y * (β : MulAut Vt)⁻¹ := hβconj ⟨y, hy⟩
    have hdy' : d * y = (β : MulAut Vt) * y * (β : MulAut Vt)⁻¹ * d := by
      have := congrArg (fun z => z * d) hdy
      simpa [mul_assoc] using this
    have hκy : κ * y = y * κ := by
      dsimp [κ]
      calc (β : MulAut Vt)⁻¹ * d * y = (β : MulAut Vt)⁻¹ * (d * y) := by group
        _ = (β : MulAut Vt)⁻¹ * ((β : MulAut Vt) * y * (β : MulAut Vt)⁻¹ * d) := by
              rw [hdy']
        _ = y * ((β : MulAut Vt)⁻¹ * d) := by group
    exact hκy.symm
  have hκnot : κ ∉ centSub Wt := by
    intro hκ
    apply hdn
    rw [mem_centSub]
    intro w hw
    have hκw : κ w = w := (mem_centSub.mp hκ) w hw
    have h1 : (β : MulAut Vt) (κ w) = d w := by
      dsimp [κ]
      simp
    rw [hκw, hβfixWt w hw] at h1
    exact h1.symm
  have hκ7 : κ ^ 7 = 1 := by
    have hcommβd : Commute ((β : MulAut Vt)⁻¹) d := by
      have h : Commute (β : MulAut Vt) d := hdβcomm.symm
      exact h.inv_left
    calc κ ^ 7 = ((β : MulAut Vt)⁻¹ * d) ^ 7 := rfl
      _ = ((β : MulAut Vt)⁻¹) ^ 7 * d ^ 7 := hcommβd.mul_pow 7
      _ = ((β : MulAut Vt) ^ 7)⁻¹ * d ^ 7 := by rw [inv_pow]
      _ = 1 := by rw [hβ7, hd7, inv_one, one_mul]
  have hκ1 : κ ≠ 1 := by
    intro h
    apply hκnot
    rw [h]
    exact (centSub Wt).one_mem
  have hκord : orderOf κ = 7 := by
    have hdvd : orderOf κ ∣ 7 := orderOf_dvd_iff_pow_eq_one.2 hκ7
    rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hκ1
    · exact h
  exact ⟨κ, hκM, hκcentL, hκcentB, hκord, hκnot⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
