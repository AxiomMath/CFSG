module

public import CFSG.LargeExtraspecial.O62Check

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check

@[expose] def s16c1b_gens : List (List ℕ) :=
  [[49, 18], [50, 17], [53, 22], [57, 26], [49, 22], [50, 21]]

@[expose] def s16c1b_invC (w : List ℕ) : ℕ := wordC w.reverse

@[expose] def s16c1b_step (gens l : List ℕ) : List ℕ :=
  gens.foldl (fun acc g => l.foldl (fun acc' x =>
    if acc'.contains (mul g x) then acc' else acc' ++ [mul g x]) acc) l

@[expose] def s16c1b_iter (gens : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, l => l
  | n + 1, l => s16c1b_iter gens n (s16c1b_step gens l)

@[expose] def s16c1b_S0 : List ℕ := s16c1b_iter (s16c1b_gens.map wordC) 6 [one]

@[expose] def s16c1b_okWord (w : List ℕ) : Bool := (w.all fun n => qB true n) && w.length % 2 == 0

@[expose] def s16c1b_A : List (List ℕ) :=
  [[3776990419, 3853274583, 8077724887, 8152960467, 34630287489, 34706571653, 38931021957,
    39006257537],
   [3793765619, 3870049783, 8094238195, 8169997559, 34630287489, 34706571653, 38930760065,
    39006519429],
   [34630287489, 34632122757, 34706571653, 34706833537, 35167158338, 35168993606, 35243442502,
    35243704386]]

@[expose] def s16c1b_checkA : Bool :=
  s16c1b_A.length == 3 &&
    s16c1b_A.all fun a => a.length == 8 && a.contains one &&
      (a.all fun x => s16c1b_S0.contains x && mul x x == one) &&
        a.all fun x => a.all fun y => a.contains (mul x y)

theorem s16c1b_checkA_ok : s16c1b_checkA = true := by decide +kernel

@[expose] def s16c1b_fixMask (c : ℕ) : ℕ :=
  (List.range 64).foldl (fun acc w => if act c w == w then acc ||| (1 <<< w) else acc) 0

@[expose] def s16c1b_tab : List (ℕ × ℕ) :=
  (s16c1b_S0.filter isInv).map fun c => (c, s16c1b_fixMask c)

@[expose] def s16c1b_fixM (c : ℕ) : ℕ :=
  if c == one then 2 ^ 64 - 1 else ((s16c1b_tab.find? fun p => p.1 == c).map Prod.snd).getD 0

@[expose] def s16c1b_prodSub (xs : List ℕ) (I : ℕ) : ℕ :=
  (List.range xs.length).foldl (fun acc i => if I.testBit i then mul acc (xs.getD i 0) else acc) one

@[expose] def s16c1b_par (m I k : ℕ) : Bool :=
  ((List.range k).filter fun i => (I &&& m).testBit i).length % 2 == 1

@[expose] def s16c1b_maskOver (xs : List ℕ) (p : ℕ → Bool) : ℕ :=
  (List.range (2 ^ xs.length)).foldl
    (fun acc I => if p I then acc &&& s16c1b_fixM (s16c1b_prodSub xs I) else acc) (2 ^ 64 - 1)

@[expose] def s16c1b_a2Prop (xs : List ℕ) : Bool :=
  (List.range (2 ^ xs.length)).all fun m => m == 0 ||
    s16c1b_maskOver xs (fun I => !s16c1b_par m I xs.length) ==
      s16c1b_maskOver xs (fun _ => true)

@[expose] def s16c1b_inA (sp : List ℕ) : Bool :=
  s16c1b_A.any fun a => sp.all (a.contains ·) && a.all (sp.contains ·)

@[expose] def s16c1b_extOK (xs : List ℕ) (x : ℕ) : Bool :=
  (xs.all fun y => y < x) && (xs.all fun y => comm x y) && !(spanC xs).contains x

@[expose] def s16c1b_dfs (invs : List ℕ) : ℕ → List ℕ → Bool
  | 0, xs => (xs.isEmpty || !s16c1b_a2Prop xs || s16c1b_inA (spanC xs)) &&
      invs.all fun x => !s16c1b_extOK xs x
  | n + 1, xs => (xs.isEmpty || !s16c1b_a2Prop xs || s16c1b_inA (spanC xs)) &&
      invs.all fun x => !s16c1b_extOK xs x || s16c1b_dfs invs n (x :: xs)

@[expose] def s16c1b_checkClassify : Bool := s16c1b_dfs (s16c1b_S0.filter isInv) 4 []

private def s16c1b_invsL : List ℕ := [
  3776990419, 3793765619, 3853274583, 3911352027, 8077724887, 8094238195, 35167158338,
  34706571653, 34764649097, 38931021957, 35243442502, 35301519946, 38930760065, 35428137838,
  39006257537, 35243704386, 3870049783, 3928127227, 3467540284, 8152960467, 8169997559,
  3450765084, 34891266989, 39006519429, 34706833537, 35168993606, 34632122757
]

private def s16c1b_tabL : List (ℕ × ℕ) := [
  (3776990419, 2459678465339953425), (3793765619, 4919206811265011985),
  (3853274583, 4909505820175403025), (3911352027, 4774405046930801025),
  (8077724887, 1234624601045344785), (8094238195, 1244157366855943185),
  (35167158338, 168882409085337), (34706571653, 28711104761168025),
  (34764649097, 434044348448246025), (38931021957, 47851476190822485),
  (35243442502, 7349875250709921945), (35301519946, 6944560561281566985),
  (38930760065, 57421771425644595), (35428137838, 6919376247441494025),
  (39006257537, 14356099998941235), (35243704386, 11024812547499884697),
  (3870049783, 2469117772662212625), (3928127227, 2604232976996925825),
  (3467540284, 2612792675017169025), (8152960467, 9809440906166944785),
  (8169997559, 9819048438768214545), (3450765084, 4766076246352337025),
  (34891266989, 459525530427887625), (39006519429, 23926103175987285),
  (34706833537, 1095216660735), (35168993606, 112807316055705), (34632122757, 43066328576753817)
]

private theorem s16c1b_invs_eq : s16c1b_S0.filter isInv = s16c1b_invsL := by decide +kernel

private theorem s16c1b_tab_eq : s16c1b_tab = s16c1b_tabL := by decide +kernel

private def s16c1b_fixMG (tab : List (ℕ × ℕ)) (c : ℕ) : ℕ :=
  if c == one then 2 ^ 64 - 1 else ((tab.find? fun p => p.1 == c).map Prod.snd).getD 0

private def s16c1b_maskOverG (tab : List (ℕ × ℕ)) (xs : List ℕ) (p : ℕ → Bool) : ℕ :=
  (List.range (2 ^ xs.length)).foldl
    (fun acc I => if p I then acc &&& s16c1b_fixMG tab (s16c1b_prodSub xs I) else acc) (2 ^ 64 - 1)

private def s16c1b_a2PropG (tab : List (ℕ × ℕ)) (xs : List ℕ) : Bool :=
  (List.range (2 ^ xs.length)).all fun m => m == 0 ||
    s16c1b_maskOverG tab xs (fun I => !s16c1b_par m I xs.length) ==
      s16c1b_maskOverG tab xs (fun _ => true)

private def s16c1b_dfsG (tab : List (ℕ × ℕ)) (invs : List ℕ) : ℕ → List ℕ → Bool
  | 0, xs => (xs.isEmpty || !s16c1b_a2PropG tab xs || s16c1b_inA (spanC xs)) &&
      invs.all fun x => !s16c1b_extOK xs x
  | n + 1, xs => (xs.isEmpty || !s16c1b_a2PropG tab xs || s16c1b_inA (spanC xs)) &&
      invs.all fun x => !s16c1b_extOK xs x || s16c1b_dfsG tab invs n (x :: xs)

private theorem s16c1b_dfs_eq (invs : List ℕ) :
    ∀ n xs, s16c1b_dfs invs n xs = s16c1b_dfsG s16c1b_tab invs n xs
  | 0, _ => rfl
  | n + 1, xs => by
    simp only [s16c1b_dfs, s16c1b_dfsG, s16c1b_dfs_eq invs n] <;> rfl

private def s16c1b_top (x : ℕ) : Bool :=
  !s16c1b_extOK [] x || s16c1b_dfsG s16c1b_tabL s16c1b_invsL 3 [x]

private theorem s16c1b_top_0 : [3776990419].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_1 : [3793765619].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_2 : [3853274583].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_3 : [3911352027, 8077724887, 8094238195].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_4 : [35167158338, 34706571653, 34764649097].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_5 : [38931021957, 35243442502, 35301519946].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_6 : [38930760065, 35428137838, 39006257537].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_7 : [35243704386, 3870049783, 3928127227].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_8 : [3467540284, 8152960467, 8169997559].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_9 : [3450765084, 34891266989, 39006519429].all s16c1b_top = true := by
  decide +kernel

private theorem s16c1b_top_10 : [34706833537, 35168993606, 34632122757].all s16c1b_top = true := by
  decide +kernel

theorem s16c1b_checkClassify_ok : s16c1b_checkClassify = true := by
  unfold s16c1b_checkClassify
  rw [s16c1b_dfs_eq, s16c1b_invs_eq, s16c1b_tab_eq, s16c1b_dfsG.eq_2]
  have hs : s16c1b_invsL = [3776990419] ++
      ([3793765619] ++
      ([3853274583] ++
      ([3911352027, 8077724887, 8094238195] ++
      ([35167158338, 34706571653, 34764649097] ++
      ([38931021957, 35243442502, 35301519946] ++
      ([38930760065, 35428137838, 39006257537] ++
      ([35243704386, 3870049783, 3928127227] ++
      ([3467540284, 8152960467, 8169997559] ++
      ([3450765084, 34891266989, 39006519429] ++
      ([34706833537, 35168993606, 34632122757])))))))))) := rfl
  have hb : (([] : List ℕ).isEmpty || !s16c1b_a2PropG s16c1b_tabL [] ||
      s16c1b_inA (spanC [])) = true := rfl
  rw [hb, show (s16c1b_invsL.all fun x => !s16c1b_extOK [] x ||
      s16c1b_dfsG s16c1b_tabL s16c1b_invsL 3 [x]) = s16c1b_invsL.all s16c1b_top from rfl, hs]
  simp only [List.all_append, s16c1b_top_0, s16c1b_top_1, s16c1b_top_2, s16c1b_top_3, s16c1b_top_4, s16c1b_top_5, s16c1b_top_6, s16c1b_top_7, s16c1b_top_8, s16c1b_top_9, s16c1b_top_10, Bool.and_self]

@[expose] def s16c1b_orbSize (w : ℕ) : ℕ := ((s16c1b_S0.map fun s => act s w).eraseDups).length

@[expose] def s16c1b_checkOrb : Bool :=
  (List.range 64).all fun w => w == 0 || qB true w || 4 < s16c1b_orbSize w ||
    s16c1b_A.all fun a => a.all fun c => act c w == w

theorem s16c1b_checkOrb_ok : s16c1b_checkOrb = true := by decide +kernel

@[expose] def s16c1b_conjC (n : List ℕ) (c : ℕ) : ℕ := mul (wordC n) (mul c (wordC n.reverse))

@[expose] def s16c1b_sameSet (l l' : List ℕ) : Bool :=
  l.all (l'.contains ·) && l'.all (l.contains ·)

@[expose] def s16c1b_Q : List ℕ := s16c1b_iter (s16c1b_A.flatten.eraseDups) 6 [one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
