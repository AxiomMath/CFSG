module

public import Certificates.Data.Kernel.E6WK

public section

universe u

namespace CFSG.KC.TwE6Det

open CFSG.KC.E6WK CFSG.StandardType.TwE6RootKill

@[expose] def letN {α : Sort u} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] def lnT (T L : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.add 64 (Nat.mul 32 L))) 4294967295

@[expose] def crd (vp r i : Nat) : Nat := vp / 2 ^ (24 * r) % 2 ^ 24 / 16 ^ i % 16

@[expose] def blk (vp k r : Nat) : Nat :=
  (List.range 6).foldr (fun i acc =>
    let o := if i = k then 10 else 8
    acc + (crd vp r i + 2 ^ 32 - o) % 2 ^ 32 * 2 ^ (32 * i) +
      (o + 2 ^ 32 - crd vp r i) % 2 ^ 32 * 2 ^ (192 + 32 * i)) 0

@[expose] def rt (vp : Nat) : Nat :=
  (List.range 432).foldr (fun b acc =>
    letN (blk vp (b / 72) (b % 72)) fun x => letN acc fun a => a + x * 2 ^ (384 * b)) 0

@[expose] def salt0 (p v : Nat) : Nat := (p + v * 6364136223846793005) % 18446744073709551616

@[expose] def tabA (RT p v : Nat) : Nat :=
  (List.range 6).foldr (fun k acc =>
    letN (Nat.land (Nat.shiftRight RT
      (Nat.mul 384 (Nat.add (Nat.mul 72 k) (lane p (lane v (wkRho.getD k 0))))))
      (2 ^ 384 - 1)) fun b =>
    letN acc fun a =>
      a + Nat.shiftLeft (Nat.land b (2 ^ 192 - 1)) (64 + 192 * k) +
        Nat.shiftLeft (Nat.shiftRight b 192) (64 + 1152 + 192 * k))
    (salt0 p v + 2 ^ (64 + 32 * 72))

@[expose] def dotT (T : Nat) : List Nat → Nat
  | [] => 0
  | t :: ts => letN (dotT T ts) fun s =>
      Nat.add s (Nat.mul (lnT T (Nat.mod t 128)) (lnT T (Nat.add 72 (Nat.div t 128))))

@[expose] def stepS (T : Nat) : List (Nat × List Nat) → Nat
  | [] => T
  | (S, ts) :: sch =>
      letN (Nat.mod (dotT T ts) 4294967296) fun d =>
      letN (Nat.mod T 18446744073709551616) fun s =>
      letN (Nat.add (Nat.sub T s)
        (Nat.add (Nat.mod (Nat.add (Nat.mul s 6364136223846793005) (Nat.add d S))
          18446744073709551616)
          (Nat.shiftLeft d (Nat.add 64 (Nat.mul 32 (Nat.add 72 S)))))) fun T' =>
      stepS T' sch

@[expose] def detS (sch : List (Nat × List Nat)) (T : Nat) : Nat := lnT (stepS T sch) 135

@[expose] def absK (x : Nat) : Nat := if x < 2 ^ 31 then x else 2 ^ 32 - x

@[expose] def okD (d : Nat) : Bool :=
  (d % 13 != 0 || d == 39) && (d % 19 != 0 || d == 57)

@[expose] def chunkOK (sch : List (Nat × List Nat)) (RT p : Nat) (vs : List Nat) : Bool :=
  vs.all fun v => okD (absK (detS sch (tabA RT p v)))

@[expose] def sch : List (Nat × List Nat) :=
  [(nat_lit 1, [nat_lit 30]), (nat_lit 2, [nat_lit 31]), (nat_lit 4, [nat_lit 32]), (nat_lit 8,
    [nat_lit 33]), (nat_lit 16, [nat_lit 34]), (nat_lit 32, [nat_lit 35]), (nat_lit 3, [nat_lit
    280, nat_lit 189]), (nat_lit 5, [nat_lit 536, nat_lit 190]), (nat_lit 6, [nat_lit 537,
    nat_lit 318]), (nat_lit 9, [nat_lit 1048, nat_lit 191]), (nat_lit 10, [nat_lit 1049, nat_lit
    319]), (nat_lit 12, [nat_lit 1050, nat_lit 575]), (nat_lit 17, [nat_lit 2072, nat_lit 192]),
    (nat_lit 18, [nat_lit 2073, nat_lit 320]), (nat_lit 20, [nat_lit 2074, nat_lit 576]),
    (nat_lit 24, [nat_lit 2075, nat_lit 1088]), (nat_lit 33, [nat_lit 4120, nat_lit 193]),
    (nat_lit 34, [nat_lit 4121, nat_lit 321]), (nat_lit 36, [nat_lit 4122, nat_lit 577]),
    (nat_lit 40, [nat_lit 4123, nat_lit 1089]), (nat_lit 48, [nat_lit 4124, nat_lit 2113]),
    (nat_lit 7, [nat_lit 786, nat_lit 695, nat_lit 404]), (nat_lit 11, [nat_lit 1298, nat_lit
    1207, nat_lit 405]), (nat_lit 13, [nat_lit 1554, nat_lit 1208, nat_lit 661]), (nat_lit 14,
    [nat_lit 1555, nat_lit 1336, nat_lit 789]), (nat_lit 19, [nat_lit 2322, nat_lit 2231,
    nat_lit 406]), (nat_lit 21, [nat_lit 2578, nat_lit 2232, nat_lit 662]), (nat_lit 22,
    [nat_lit 2579, nat_lit 2360, nat_lit 790]), (nat_lit 25, [nat_lit 3090, nat_lit 2233,
    nat_lit 1174]), (nat_lit 26, [nat_lit 3091, nat_lit 2361, nat_lit 1302]), (nat_lit 28,
    [nat_lit 3092, nat_lit 2617, nat_lit 1558]), (nat_lit 35, [nat_lit 4370, nat_lit 4279,
    nat_lit 407]), (nat_lit 37, [nat_lit 4626, nat_lit 4280, nat_lit 663]), (nat_lit 38,
    [nat_lit 4627, nat_lit 4408, nat_lit 791]), (nat_lit 41, [nat_lit 5138, nat_lit 4281,
    nat_lit 1175]), (nat_lit 42, [nat_lit 5139, nat_lit 4409, nat_lit 1303]), (nat_lit 44,
    [nat_lit 5140, nat_lit 4665, nat_lit 1559]), (nat_lit 49, [nat_lit 6162, nat_lit 4282,
    nat_lit 2199]), (nat_lit 50, [nat_lit 6163, nat_lit 4410, nat_lit 2327]), (nat_lit 52,
    [nat_lit 6164, nat_lit 4666, nat_lit 2583]), (nat_lit 56, [nat_lit 6165, nat_lit 5178,
    nat_lit 3095]), (nat_lit 15, [nat_lit 1804, nat_lit 1713, nat_lit 1422, nat_lit 947]),
    (nat_lit 23, [nat_lit 2828, nat_lit 2737, nat_lit 2446, nat_lit 948]), (nat_lit 27, [nat_lit
    3340, nat_lit 3249, nat_lit 2447, nat_lit 1460]), (nat_lit 29, [nat_lit 3596, nat_lit 3250,
    nat_lit 2703, nat_lit 1716]), (nat_lit 30, [nat_lit 3597, nat_lit 3378, nat_lit 2831,
    nat_lit 1844]), (nat_lit 39, [nat_lit 4876, nat_lit 4785, nat_lit 4494, nat_lit 949]),
    (nat_lit 43, [nat_lit 5388, nat_lit 5297, nat_lit 4495, nat_lit 1461]), (nat_lit 45,
    [nat_lit 5644, nat_lit 5298, nat_lit 4751, nat_lit 1717]), (nat_lit 46, [nat_lit 5645,
    nat_lit 5426, nat_lit 4879, nat_lit 1845]), (nat_lit 51, [nat_lit 6412, nat_lit 6321,
    nat_lit 4496, nat_lit 2485]), (nat_lit 53, [nat_lit 6668, nat_lit 6322, nat_lit 4752,
    nat_lit 2741]), (nat_lit 54, [nat_lit 6669, nat_lit 6450, nat_lit 4880, nat_lit 2869]),
    (nat_lit 57, [nat_lit 7180, nat_lit 6323, nat_lit 5264, nat_lit 3253]), (nat_lit 58,
    [nat_lit 7181, nat_lit 6451, nat_lit 5392, nat_lit 3381]), (nat_lit 60, [nat_lit 7182,
    nat_lit 6707, nat_lit 5648, nat_lit 3637]), (nat_lit 31, [nat_lit 3846, nat_lit 3755,
    nat_lit 3464, nat_lit 2989, nat_lit 1930]), (nat_lit 47, [nat_lit 5894, nat_lit 5803,
    nat_lit 5512, nat_lit 5037, nat_lit 1931]), (nat_lit 55, [nat_lit 6918, nat_lit 6827,
    nat_lit 6536, nat_lit 5038, nat_lit 2955]), (nat_lit 59, [nat_lit 7430, nat_lit 7339,
    nat_lit 6537, nat_lit 5550, nat_lit 3467]), (nat_lit 61, [nat_lit 7686, nat_lit 7340,
    nat_lit 6793, nat_lit 5806, nat_lit 3723]), (nat_lit 62, [nat_lit 7687, nat_lit 7468,
    nat_lit 6921, nat_lit 5934, nat_lit 3851]), (nat_lit 63, [nat_lit 7936, nat_lit 7845,
    nat_lit 7554, nat_lit 7079, nat_lit 6020, nat_lit 4009])]

@[expose] def chunk (vk : List Nat) (c : Nat) : List Nat := (vk.drop (128 * c)).take 128

@[expose] def chkAt (vp : Nat) (up vk : List Nat) (i : Nat) : Bool :=
  letN (rt vp) fun RT => chunkOK sch RT (up.getD (i / 15) 0) (chunk vk (i % 15))

end CFSG.KC.TwE6Det
