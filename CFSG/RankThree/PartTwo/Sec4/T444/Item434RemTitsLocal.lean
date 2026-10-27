module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsCheck
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM12
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemTits

open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits

theorem card_fix_of_rep {n : ℕ} {a : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n a g) :
    Fintype.card {x : Fin n // g x = x} = fixCount n a := by
  have hl : fixCount n a = (List.finRange n).countP fun x => decide (g x = x) := by
    rw [fixCount, ← List.map_coe_finRange_eq_range, List.countP_map]
    congr 1
    funext x
    rw [Bool.eq_iff_iff]
    simp [h x, Fin.ext_iff]
  rw [hl, Fintype.card_subtype, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  simp

section Syl


theorem lettersOK_of_mem {w : List ℤ} (hw : w ∈ sylWords) : lettersOK 13 w = true := by
  have hp : ∀ v, lettersOK 13 v = true → ∀ n, lettersOK 13 (powWord v n) = true := by
    intro v hv n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [powWord, lettersOK, List.all_append, Bool.and_eq_true] at hv ih ⊢
      exact ⟨hv, ih⟩
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw
  have hx : lettersOK 13 xWord = true := by decide +kernel
  have hy : lettersOK 13 yWord = true := by decide +kernel
  have hz : lettersOK 13 zWord = true := by decide +kernel
  have h1 := hp _ hx (k / 9)
  have h2 := hp _ hy (k / 3 % 3)
  have h3 := hp _ hz (k % 3)
  simp only [lettersOK, List.all_append, Bool.and_eq_true] at h1 h2 h3 ⊢
  exact ⟨⟨h1, h2⟩, h3⟩

theorem rep_of_mem {w : List ℤ} (hw : w ∈ sylWords) :
    Rep 1755 (wordArr 1755 titsDerivedArrs w) (wordIn 13 titsT w) :=
  rep_wordArr_titsT (lettersOK_of_mem hw)

theorem mul_mem_sylPerms {g h : Equiv.Perm (Fin 1755)} (hg : g ∈ sylPerms)
    (hh : h ∈ sylPerms) : g * h ∈ sylPerms :=
  tits_three_check.2.1 g hg h hh

theorem cube_of_mem_sylPerms {g : Equiv.Perm (Fin 1755)} (hg : g ∈ sylPerms) :
    g * g * g = 1 := by
  rw [← pow_three']
  exact tits_three_check.2.2.1 g hg

theorem length_sylPerms : sylPerms.length = 27 := by
  rw [sylPerms, List.length_map, sylWords, List.length_map, List.length_range]

@[expose] def sylGrp : Subgroup (Equiv.Perm (Fin 1755)) where
  carrier := {g | g ∈ sylPerms}
  mul_mem' hg hh := mul_mem_sylPerms hg hh
  one_mem' := by
    have h0 : sylPerms ≠ [] := by
      intro h
      have := length_sylPerms
      rw [h] at this
      exact absurd this (by norm_num)
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ h0
    change (1 : Equiv.Perm (Fin 1755)) ∈ sylPerms
    rw [← cube_of_mem_sylPerms hg]
    exact mul_mem_sylPerms (mul_mem_sylPerms hg hg) hg
  inv_mem' {g} hg := by
    have hinv : g⁻¹ = g * g :=
      inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact cube_of_mem_sylPerms hg)
    change g⁻¹ ∈ sylPerms
    rw [hinv]
    exact mul_mem_sylPerms hg hg

theorem mem_sylGrp {g : Equiv.Perm (Fin 1755)} : g ∈ sylGrp ↔ g ∈ sylPerms := Iff.rfl

theorem sylPerms_nodup : sylPerms.Nodup :=
  tits_three_check.1

theorem card_sylGrp : Nat.card sylGrp = 27 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  change ({g | g ∈ sylPerms} : Set (Equiv.Perm (Fin 1755))).ncard = 27
  rw [ncard_list_set sylPerms_nodup, length_sylPerms]

theorem sylGrp_le_titsD : sylGrp ≤ titsD := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 (mem_sylGrp.1 hg)
  exact wordIn_titsT_mem_titsD w

theorem exists_not_commute_sylGrp : ∃ g ∈ sylGrp, ∃ h ∈ sylGrp, g * h ≠ h * g :=
  tits_three_check.2.2.2.1

theorem lines_of_mem_sylGrp
    {g : Equiv.Perm (Fin 1755)} (hg : g ∈ sylGrp) (hg1 : g ≠ 1) :
    ¬ 5 ∣ Fintype.card {p : Fin 2925 // titsDLineAct ⟨g, sylGrp_le_titsD hg⟩ p = p} ∧
      ¬ 13 ∣ Fintype.card {p : Fin 2925 // titsDLineAct ⟨g, sylGrp_le_titsD hg⟩ p = p} := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (mem_sylGrp.1 hg)
  have hact : titsDLineAct ⟨wordIn 13 titsT w, sylGrp_le_titsD hg⟩ = wordIn 13 titsTStar w :=
    titsDLineAct_word w
  rw [hact]
  exact tits_three_check.2.2.2.2.1 w hw hg1

end Syl

theorem factorization_card_titsD :
    (Nat.card titsD).factorization 3 = 3 := by
  rw [card_titsD, show (17971200 : ℕ) = 3 ^ 3 * 665600 by norm_num]
  exact Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)

@[expose] noncomputable def sylD :
    Subgroup titsD :=
  sylGrp.subgroupOf titsD

theorem card_sylD :
    Nat.card sylD = 3 ^ (Nat.card titsD).factorization 3 := by
  rw [sylD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylGrp_le_titsD).toEquiv, card_sylGrp,
    factorization_card_titsD]
  norm_num

@[expose] noncomputable def sylSylow :
    Sylow 3 titsD :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard sylD card_sylD

theorem exists_conj_mem_sylGrp
    {x : titsD} (hx : orderOf x = 3) :
    ∃ g : titsD, ((g * x * g⁻¹ : titsD) : Equiv.Perm (Fin 1755)) ∈ sylGrp := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow sylSylow (x := x)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]))
  exact ⟨g, hg⟩

theorem orderOf_conj {X : Type*} [Group X] (g x : X) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using h

theorem orderOf_dvd_of_fix_line
    {y : titsD} {a : Fin 2925}
    (ha : titsDLineAct y a = a) : orderOf y ∣ 6144 := by
  obtain ⟨k, hk⟩ := titsDLine_transitive a
  have hstab : k⁻¹ * y * k ∈ titsLineStab := by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, map_mul, map_mul, map_inv,
      Equiv.Perm.smul_def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hk, ha, ← hk]
    simp
  have h := orderOf_dvd_natCard (⟨k⁻¹ * y * k, hstab⟩ : titsLineStab)
  rwa [Subgroup.orderOf_mk, card_titsLineStab, show k⁻¹ * y * k = k⁻¹ * y * k⁻¹⁻¹ by
    rw [inv_inv], orderOf_conj] at h

theorem mul_ne_mul_of_orderOf
    {x y : titsD} (hx : orderOf x = 3) {r : ℕ} (hr : r = 5 ∨ r = 13) (hy : orderOf y = r) :
    x * y ≠ y * x := by
  intro hxy
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> norm_num
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylGrp hx
  set s := g * x * g⁻¹ with hs
  set y' := g * y * g⁻¹ with hy'
  have hsy : s * y' = y' * s := by
    calc s * y' = g * (x * y) * g⁻¹ := by rw [hs, hy']; group
      _ = g * (y * x) * g⁻¹ := by rw [hxy]
      _ = y' * s := by rw [hs, hy']; group
  have hs1 : (s : Equiv.Perm (Fin 1755)) ≠ 1 := by
    intro h
    have h1 : s = 1 := Subtype.ext h
    have := orderOf_conj g x
    rw [← hs, h1, orderOf_one, hx] at this
    exact absurd this (by norm_num)
  obtain ⟨h5, h13⟩ := lines_of_mem_sylGrp hg hs1
  have hρs : titsDLineAct ⟨(s : Equiv.Perm (Fin 1755)), sylGrp_le_titsD hg⟩ = titsDLineAct s :=
    rfl
  rw [hρs] at h5 h13
  have hcard : ¬ r ∣ Fintype.card {p : Fin 2925 // titsDLineAct s p = p} := by
    rcases hr with rfl | rfl
    · exact h5
    · exact h13
  set f := titsDLineAct y' with hf
  set e := titsDLineAct s with he
  have hfe : e * f = f * e := by rw [hf, he, ← map_mul, ← map_mul, hsy]
  have hinv : ∀ p, e (f p) = f p ↔ e p = p := by
    intro p
    have hc : e (f p) = f (e p) := by
      have := congrArg (fun σ : Equiv.Perm (Fin 2925) => σ p) hfe
      simpa only [Equiv.Perm.mul_apply] using this
    rw [hc]
    exact ⟨fun h => f.injective h, fun h => by rw [h]⟩
  have hfr : f ^ r = 1 := by
    rw [hf, ← map_pow, ← hy, ← orderOf_conj g y, ← hy', pow_orderOf_eq_one, map_one]
  have hσ : (f.subtypePerm (p := fun q => e q = q) hinv) ^ r ^ 1 = 1 := by
    rw [pow_one, Equiv.Perm.subtypePerm_pow]
    ext ⟨p, hp⟩
    simp [hfr]
  obtain ⟨⟨a, _⟩, hσa⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  have hfa : f a = a := congrArg Subtype.val hσa
  have hdvd := orderOf_dvd_of_fix_line hfa
  rw [hy', orderOf_conj, hy] at hdvd
  rcases hr with rfl | rfl <;> norm_num at hdvd

theorem bOne_rep :
    Rep 1755 bOneArr bOne :=
  rep_wordArr_titsT (by decide +kernel)

theorem bOne_mem_titsD : bOne ∈ titsD :=
  wordIn_titsT_mem_titsD _

theorem bOne_comm :
    bOne * titsTInv = titsTInv * bOne :=
  tits_three_check.2.2.2.2.2.2.2.1

theorem bOne_cube :
    bOne * bOne * bOne = 1 := by
  rw [← pow_three']
  exact tits_three_check.2.2.2.2.2.2.1

theorem bOne_ne_one :
    bOne ≠ 1 :=
  tits_three_check.2.2.2.2.2.1

theorem eq_t_of_mem_titsN
    {n : Equiv.Perm (Fin 1755)} (hn : n ∈ titsN) (ht : n * titsTInv = titsTInv * n)
    (hb : n * bOne = bOne * n) (h2 : n * n = 1) (h1 : n ≠ 1) : n = titsTInv :=
  (tits_three_check.2.2.2.2.2.2.2.2 n hn h2 ht hb).resolve_left h1

theorem card_centralizer_eq_of_isConj {X : Type*} [Group X] {a b : X} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set X)) =
      Nat.card (Subgroup.centralizer ({b} : Set X)) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  rw [← hg, ← CFSG.Sporadic.Schreier.Tits.map_conj_centralizer g a,
    Subgroup.card_map_of_injective
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]

theorem eq_of_commute_of_orderOf_three
    {x u v : titsD} (hx : orderOf x = 3) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (hux : u * x = x * u) (hvx : v * x = x * v) (huv : u * v = v * u) : u = v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases titsD_involution_conj u hu with hz | ht
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 hz
    have hz' : titsZD = c⁻¹ * u * c := by rw [← hc]; group
    have hmem : c⁻¹ * x * c ∈ Subgroup.centralizer ({titsZD} : Set titsD) := by
      rw [Subgroup.mem_centralizer_singleton_iff, hz']
      calc c⁻¹ * x * c * (c⁻¹ * u * c) = c⁻¹ * (x * u) * c := by group
        _ = c⁻¹ * (u * x) * c := by rw [hux]
        _ = c⁻¹ * u * c * (c⁻¹ * x * c) := by group
    have h3 := orderOf_dvd_natCard (⟨_, hmem⟩ : Subgroup.centralizer ({titsZD} : Set titsD))
    rw [Subgroup.orderOf_mk, show c⁻¹ * x * c = c⁻¹ * x * c⁻¹⁻¹ by rw [inv_inv], orderOf_conj,
      hx, card_centralizer_titsZD] at h3
    norm_num at h3
  · obtain ⟨c, hc⟩ := isConj_iff.1 ht
    have ht' : titsTD = c⁻¹ * u * c := by rw [← hc]; group
    have hx't : c⁻¹ * x * c * titsTD = titsTD * (c⁻¹ * x * c) := by
      rw [ht']
      calc c⁻¹ * x * c * (c⁻¹ * u * c) = c⁻¹ * (x * u) * c := by group
        _ = c⁻¹ * (u * x) * c := by rw [hux]
        _ = c⁻¹ * u * c * (c⁻¹ * x * c) := by group
    have hv't : c⁻¹ * v * c * titsTD = titsTD * (c⁻¹ * v * c) := by
      rw [ht']
      calc c⁻¹ * v * c * (c⁻¹ * u * c) = c⁻¹ * (v * u) * c := by group
        _ = c⁻¹ * (u * v) * c := by rw [huv]
        _ = c⁻¹ * u * c * (c⁻¹ * v * c) := by group
    have hx'v' : c⁻¹ * v * c * (c⁻¹ * x * c) = c⁻¹ * x * c * (c⁻¹ * v * c) := by
      calc c⁻¹ * v * c * (c⁻¹ * x * c) = c⁻¹ * (v * x) * c := by group
        _ = c⁻¹ * (x * v) * c := by rw [hvx]
        _ = c⁻¹ * x * c * (c⁻¹ * v * c) := by group
    have hCt := (titsD_centralizer_t).1
    have memC : ∀ w : titsD, w * titsTD = titsTD * w → (w : Equiv.Perm (Fin 1755)) ∈ titsCt := by
      intro w hw
      rw [hCt]
      exact ⟨w.2, Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hw)⟩
    have hbC : bOne ∈ titsCt := by
      rw [hCt]
      exact ⟨bOne_mem_titsD, Subgroup.mem_centralizer_singleton_iff.2 bOne_comm⟩
    set X : titsCt := ⟨_, memC _ hx't⟩ with hX
    set V : titsCt := ⟨_, memC _ hv't⟩ with hV
    set B : titsCt := ⟨bOne, hbC⟩ with hB
    have hXo : orderOf X = 3 := by
      rw [hX, Subgroup.orderOf_mk, Subgroup.orderOf_coe, show c⁻¹ * x * c = c⁻¹ * x * c⁻¹⁻¹ by
        rw [inv_inv], orderOf_conj, hx]
    have hVo : orderOf V = 2 := by
      rw [hV, Subgroup.orderOf_mk, Subgroup.orderOf_coe, show c⁻¹ * v * c = c⁻¹ * v * c⁻¹⁻¹ by
        rw [inv_inv], orderOf_conj, hv]
    have hBo : orderOf B = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        rw [Subgroup.coe_pow, pow_three, ← mul_assoc]
        exact bOne_cube
      · intro h
        exact bOne_ne_one (congrArg Subtype.val h)
    have hXV : V * X = X * V := Subtype.ext (by
      simp only [Subgroup.coe_mul, hX, hV]
      exact congrArg Subtype.val hx'v')
    have hCcard : (Nat.card titsCt).factorization 3 = 1 := by
      rw [card_titsCt, show (1536 : ℕ) = 3 ^ 1 * 512 by norm_num]
      exact Item434AltPerm.factorization_three_pow_mul 1 (by norm_num)
    have hBcard : Nat.card (Subgroup.zpowers B) = 3 ^ (Nat.card titsCt).factorization 3 := by
      rw [Nat.card_zpowers, hBo, hCcard, pow_one]
    obtain ⟨d, hd⟩ := exists_conj_mem_sylow (Sylow.ofCard _ hBcard) (x := X)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hXo, pow_one]))
    rw [Sylow.coe_ofCard] at hd
    have hX''o : orderOf (d * X * d⁻¹) = 3 := by rw [orderOf_conj, hXo]
    have hzp : Subgroup.zpowers (d * X * d⁻¹) = Subgroup.zpowers B :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hd)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hX''o, hBo])
    have hBmem : B ∈ Subgroup.zpowers (d * X * d⁻¹) := hzp ▸ Subgroup.mem_zpowers B
    have hV''X : d * V * d⁻¹ * (d * X * d⁻¹) = d * X * d⁻¹ * (d * V * d⁻¹) := by
      calc d * V * d⁻¹ * (d * X * d⁻¹) = d * (V * X) * d⁻¹ := by group
        _ = d * (X * V) * d⁻¹ := by rw [hXV]
        _ = d * X * d⁻¹ * (d * V * d⁻¹) := by group
    have hV''B : d * V * d⁻¹ * B = B * (d * V * d⁻¹) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hBmem
      rw [← hk]
      exact ((Commute.zpow_right (show Commute (d * V * d⁻¹) (d * X * d⁻¹) from hV''X) k)).eq
    set n := ((d * V * d⁻¹ : titsCt) : Equiv.Perm (Fin 1755)) with hn
    have hnN : n ∈ titsN := (d * V * d⁻¹).2.1
    have hnt : n * titsTInv = titsTInv * n :=
      Subgroup.mem_centralizer_singleton_iff.1 (d * V * d⁻¹).2.2
    have hnb : n * bOne = bOne * n := congrArg Subtype.val hV''B
    have hV''o : orderOf (d * V * d⁻¹) = 2 := by rw [orderOf_conj, hVo]
    have hn2 : n * n = 1 := by
      rw [hn, ← Subgroup.coe_mul, ← pow_two, ← hV''o, pow_orderOf_eq_one, Subgroup.coe_one]
    have hn1 : n ≠ 1 := by
      intro h
      have h1 : d * V * d⁻¹ = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hV''o
      exact absurd hV''o (by norm_num)
    have hnT := eq_t_of_mem_titsN hnN hnt hnb hn2 hn1
    have hdt : (d : Equiv.Perm (Fin 1755)) * titsTInv = titsTInv * d :=
      Subgroup.mem_centralizer_singleton_iff.1 d.2.2
    have hVt : ((V : titsCt) : Equiv.Perm (Fin 1755)) = titsTInv := by
      have e1 : ((V : titsCt) : Equiv.Perm (Fin 1755)) = (d : Equiv.Perm (Fin 1755))⁻¹ * n * d := by
        rw [hn]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1, hnT, mul_assoc, ← hdt, ← mul_assoc, inv_mul_cancel, one_mul]
    have hv'T : c⁻¹ * v * c = titsTD := Subtype.ext hVt
    calc u = c * titsTD * c⁻¹ := hc.symm
      _ = c * (c⁻¹ * v * c) * c⁻¹ := by rw [hv'T]
      _ = v := by group

theorem card_centralizer_of_involution
    {u : titsD} (hu : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set titsD)) = 10240 ∨
      Nat.card (Subgroup.centralizer ({u} : Set titsD)) = 1536 := by
  rcases titsD_involution_conj u hu with hz | ht
  · exact Or.inl (by rw [← card_centralizer_eq_of_isConj hz, card_centralizer_titsZD])
  · exact Or.inr (by rw [← card_centralizer_eq_of_isConj ht, (titsD_centralizer_t).2.1])

theorem false_of_commute_e9
    {P : Subgroup titsD} (hP9 : Nat.card P = 9) {u : titsD} (hu : orderOf u = 2)
    (hc : ∀ p ∈ P, p * u = u * p) : False := by
  have hle : P ≤ Subgroup.centralizer ({u} : Set titsD) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.2 (hc p hp)
  have hdvd : 9 ∣ Nat.card (Subgroup.centralizer ({u} : Set titsD)) :=
    hP9 ▸ Subgroup.card_dvd_of_le hle
  rcases card_centralizer_of_involution hu with h | h <;> rw [h] at hdvd <;> norm_num at hdvd

theorem eq_bot_of_le_normalizer
    {P W : Subgroup titsD} (hPe : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9)
    (hW3 : ¬ 3 ∣ Nat.card W) (hN : P ≤ Subgroup.normalizer (W : Set titsD)) : W = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 3 (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hPe (by rw [hP9]; norm_num) hN hcop
    ?_
  intro b hb hb1
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hPe.2 b hb) hb1
  set Y := W ⊓ Subgroup.centralizer ({b} : Set titsD) with hY
  have hY2 : IsPGroup 2 Y := by
    intro y
    refine ⟨11, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← orderOf_dvd_iff_pow_eq_one]
    have hyb : (y : titsD) * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 y.2.2
    have hyW : orderOf (y : titsD) ∣ Nat.card W := by
      have := orderOf_dvd_natCard (⟨(y : titsD), y.2.1⟩ : W)
      rwa [Subgroup.orderOf_mk] at this
    have hyD : orderOf (y : titsD) ∣ 2 ^ 11 * 8775 := by
      have := orderOf_dvd_natCard (y : titsD)
      rwa [card_titsD, show (17971200 : ℕ) = 2 ^ 11 * 8775 by norm_num] at this
    have hnot : ∀ r, r = 5 ∨ r = 13 → ¬ r ∣ orderOf (y : titsD) := by
      intro r hr hdvd
      have hr0 : r ≠ 0 := by rcases hr with rfl | rfl <;> norm_num
      have hpos : orderOf (y : titsD) ≠ 0 := (orderOf_pos _).ne'
      have hord := orderOf_pow_orderOf_div hpos hdvd
      have hcomm : b * (y : titsD) ^ (orderOf (y : titsD) / r) =
          (y : titsD) ^ (orderOf (y : titsD) / r) * b :=
        ((Commute.pow_left (show Commute (y : titsD) b from hyb) _).eq).symm
      exact mul_ne_mul_of_orderOf hb3 hr hord hcomm
    have h3 : ¬ 3 ∣ orderOf (y : titsD) := fun h => hW3 (h.trans hyW)
    have hc3 : Nat.Coprime (orderOf (y : titsD)) 27 :=
      Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    have hc5 : Nat.Coprime (orderOf (y : titsD)) 25 :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2
        (hnot 5 (Or.inl rfl))).symm
    have hc13 : Nat.Coprime (orderOf (y : titsD)) 13 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (hnot 13 (Or.inr rfl))).symm
    have hc : Nat.Coprime (orderOf (y : titsD)) 8775 := by
      rw [show (8775 : ℕ) = 27 * 25 * 13 by norm_num]
      exact (hc3.mul_right hc5).mul_right hc13
    exact hc.dvd_of_dvd_mul_right hyD
  rintro x ⟨hxW, hxC⟩
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hYnt : Nontrivial Y :=
    ⟨⟨⟨x, hxW, hxC⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have hZnt : Nontrivial (Subgroup.center Y) := hY2.center_nontrivial
  obtain ⟨k, hk0, hk⟩ := (hY2.to_subgroup (Subgroup.center Y)).nontrivial_iff_card.1 hZnt
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 (G := Subgroup.center Y)
    (by rw [hk]; exact dvd_pow_self 2 hk0.ne')
  set v₀ : titsD := ((v : Y) : titsD) with hv₀
  have hv₀2 : orderOf v₀ = 2 := by rw [hv₀, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hv]
  have hv₀b : v₀ * b = b * v₀ := Subgroup.mem_centralizer_singleton_iff.1 (v : Y).2.2
  have hv₀W : v₀ ∈ W := (v : Y).2.1
  refine false_of_commute_e9 hP9 hv₀2 fun p hp => ?_
  have hpb : p * b = b * p := hPe.1.is_comm.comm ⟨p, hp⟩ ⟨b, hb⟩ |> congrArg Subtype.val
  have hwW : p * v₀ * p⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hN hp) v₀).1 hv₀W
  have hwb : p * v₀ * p⁻¹ * b = b * (p * v₀ * p⁻¹) := by
    calc p * v₀ * p⁻¹ * b = p * v₀ * (p⁻¹ * b) := by group
      _ = p * v₀ * (b * p⁻¹) := by
          rw [show p⁻¹ * b = b * p⁻¹ by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hpb, mul_assoc, mul_inv_cancel, mul_one]]
      _ = p * (v₀ * b) * p⁻¹ := by group
      _ = p * (b * v₀) * p⁻¹ := by rw [hv₀b]
      _ = (p * b) * v₀ * p⁻¹ := by group
      _ = (b * p) * v₀ * p⁻¹ := by rw [hpb]
      _ = b * (p * v₀ * p⁻¹) := by group
  have hwY : p * v₀ * p⁻¹ ∈ Y := ⟨hwW, Subgroup.mem_centralizer_singleton_iff.2 hwb⟩
  have hwv : p * v₀ * p⁻¹ * v₀ = v₀ * (p * v₀ * p⁻¹) := by
    have := Subgroup.mem_center_iff.1 v.2 ⟨_, hwY⟩
    exact congrArg Subtype.val this
  have hw2 : orderOf (p * v₀ * p⁻¹) = 2 := by rw [orderOf_conj, hv₀2]
  have heq := eq_of_commute_of_orderOf_three hb3 hw2 hv₀2 hwb hv₀b hwv
  calc p * v₀ = p * v₀ * p⁻¹ * p := by group
    _ = v₀ * p := by rw [heq]

theorem mem_range_conj_of_fix
    {P : Subgroup titsD} (hP9 : Nat.card P = 9) (α : MulAut titsD) (hα : ∀ f ∈ P, α f = f) :
    α ∈ (MulAut.conj : titsD →* MulAut titsD).range := by
  obtain ⟨a, rfl⟩ := titsConj_surjective α
  have hcomm : ∀ p ∈ P, (a : Equiv.Perm (Fin 1755)) * p = p * a := by
    intro p hp
    have h := congrArg Subtype.val (hα p hp)
    rw [coe_titsConj_apply] at h
    calc (a : Equiv.Perm (Fin 1755)) * p = a * p * (a : Equiv.Perm (Fin 1755))⁻¹ * a := by group
      _ = p * a := by rw [h]
  have hpos : orderOf a ≠ 0 := (orderOf_pos a).ne'
  have hodd : ¬ 2 ∣ orderOf a := by
    intro h2
    set u := a ^ (orderOf a / 2) with hu
    have hu2 : orderOf u = 2 := orderOf_pow_orderOf_div hpos h2
    have huD : (u : Equiv.Perm (Fin 1755)) ∈ titsD :=
      titsA_involution_mem_D u.2 (by rw [Subgroup.orderOf_coe]; exact hu2)
    refine false_of_commute_e9 hP9 (u := ⟨u, huD⟩)
      (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hu2]) fun p hp => Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [hu, Subgroup.coe_pow]
    exact ((Commute.pow_left (show Commute (a : Equiv.Perm (Fin 1755)) p from hcomm p hp)
      _).eq).symm
  have hsq : a ^ 2 ∈ titsD.subgroupOf titsA := Subgroup.sq_mem_of_index_two titsD_index a
  obtain ⟨m, hm⟩ : ∃ m, orderOf a = 2 * m + 1 := ⟨orderOf a / 2, by omega⟩
  have hapow : a = (a ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf a + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have haD : a ∈ titsD.subgroupOf titsA := by
    rw [hapow]
    exact Subgroup.pow_mem _ hsq _
  change titsConj a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner titsD
  rw [← map_titsConj_titsD]
  exact Subgroup.mem_map_of_mem _ haD

theorem false_of_e27
    {P : Subgroup titsD} (hPe : CFSG.Assembly.IsElemAbelian 3 P) (h27 : Nat.card P = 27) :
    False := by
  obtain ⟨g, hg⟩ := Item434SmallTwoOther.exists_map_conj_of_sylow card_sylD
    (by rw [h27, card_sylD, factorization_card_titsD]; norm_num)
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_commute_sylGrp
  have hxD := sylGrp_le_titsD hx
  have hyD := sylGrp_le_titsD hy
  have hxP : MulAut.conj g ⟨x, hxD⟩ ∈ P := by
    rw [hg]
    exact ⟨⟨x, hxD⟩, hx, rfl⟩
  have hyP : MulAut.conj g ⟨y, hyD⟩ ∈ P := by
    rw [hg]
    exact ⟨⟨y, hyD⟩, hy, rfl⟩
  have hc := congrArg Subtype.val (hPe.1.is_comm.comm ⟨_, hxP⟩ ⟨_, hyP⟩)
  simp only [Subgroup.coe_mul, ← map_mul] at hc
  have hc' := (MulAut.conj g).injective hc
  exact hxy (congrArg Subtype.val hc')

theorem noSignalizer
    {P : Subgroup titsD} (hPe : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    Item434SporGen.NoSignalizer P :=
  Item434SporGen.noSignalizer_of_inner titsD_center
    (fun _ hW3 hN => eq_bot_of_le_normalizer hPe hP9 hW3 hN) (mem_range_conj_of_fix hP9)

end CFSG.RankThree.PartTwo.Sec4.Item434RemTits
