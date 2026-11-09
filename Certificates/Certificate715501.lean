module

public import Certificates.Data.A3LatticeF4
public meta import Certificates.Data.A3LatticeF4

public section

open Certificates.A3LatticeF4

namespace CertificateChecks.Batch715501

open Certificates.A3LatticeF4

@[expose] def filterBy {α : Type} : List Bool → List α → List α
  | b :: bs, a :: as => if b then a :: filterBy bs as else filterBy bs as
  | _, _ => []

theorem filter_eq_filterBy {α : Type} (p : α → Bool) :
    ∀ l : List α, l.filter p = filterBy (l.map p) l
  | [] => rfl
  | a :: l => by
    cases h : p a <;> simp [List.filter_cons, filterBy, h, filter_eq_filterBy p l]

@[expose] def key (rs : List (Array Int)) (c₁ c₂ : Array Nat) : List Bool :=
  rs.map fun g => pair3 g c₁ == 0 && pair3 g c₂ == 0

@[expose] def G (rs : List (Array Int)) (k : List Bool) : Bool :=
  let ks := filterBy k rs
  ks.all fun m => let cs := comp ks m; adjClosed ks cs && cs.length != 12

@[expose] def encodeB : List Bool → Nat
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * encodeB l

@[expose] def decodeB : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: decodeB k (n / 2)

theorem decodeB_encodeB : ∀ l : List Bool, decodeB l.length (encodeB l) = l
  | [] => rfl
  | b :: l => by
    have ih := decodeB_encodeB l
    have h2 : ((if b then 1 else 0) + 2 * encodeB l) % 2 = (if b then 1 else 0) := by
      cases b <;> simp <;> omega
    have h3 : ((if b then 1 else 0) + 2 * encodeB l) / 2 = encodeB l := by
      cases b <;> simp <;> omega
    simp only [List.length_cons, decodeB, encodeB, h2, h3, ih]
    cases b <;> rfl

theorem mainCheck_of (rs : List (Array Int)) (M : List Nat)
    (h1 : (vecs.all fun c₁ => vecs.all fun c₂ =>
      !indep c₁ c₂ || M.any fun m => Nat.beq m (encodeB (key rs c₁ c₂))) = true)
    (h2 : M.all (fun m => G rs (decodeB rs.length m)) = true) : mainCheck rs = true := by
  unfold mainCheck
  rw [List.all_eq_true]
  intro c₁ hc₁
  rw [List.all_eq_true]
  intro c₂ hc₂
  have e1 := List.all_eq_true.1 (List.all_eq_true.1 h1 c₁ hc₁) c₂ hc₂
  cases hi : indep c₁ c₂
  · rfl
  · rw [hi] at e1
    have e2 : (M.any fun m => Nat.beq m (encodeB (key rs c₁ c₂))) = true := by simpa using e1
    obtain ⟨m, hm, hb⟩ := List.any_eq_true.1 e2
    have hme : m = encodeB (key rs c₁ c₂) := Nat.eq_of_beq_eq_true hb
    have hG := List.all_eq_true.1 h2 m hm
    have hlen : (key rs c₁ c₂).length = rs.length := by simp [key]
    rw [hme, ← hlen, decodeB_encodeB] at hG
    simp only [Bool.not_true, Bool.false_or]
    rw [filter_eq_filterBy]
    exact hG

@[expose] def keyCodes : List Nat := [
    265740, 2122, 8791918856, 33654920, 164806, 134742532, 8690663940, 8657043522, 33751296,
    134774912, 168625218, 8657339520, 394496, 2073, 74766790690824, 9345848838152, 533,
    9345848836612, 74766790689284, 84112639524881, 0, 263185, 74766790951936, 9345849099264,
    194613558118408, 384416352264, 2336462211080, 2164261380, 178331337097732, 19000935318020,
    2645699854336, 175924024705024, 18764712116224, 73014707200, 176231098352640, 21030324405248,
    6184, 18803083272, 271591432, 5272100, 1082130948, 17987273220, 17716744224, 274743296,
    1083187200, 1352930336, 17718060032, 4473856, 4211, 175921860444226, 18691697672258,
    18691697672209, 175921860448288, 175921860444177, 18691697676320, 2168471618, 74096574530,
    75093745074242, 310319775744, 19881000960, 74839809343488, 90731184128, 309241856000,
    74770037080064, 1056834, 11682311045186, 270532674, 9346119368704, 2336463265792,
    2336732741632, 9345849892864, 4342033, 2337544470784, 17716871424, 1216872465, 17851482112,
    2336601161728, 2362835992593, 8661254144, 9739173888, 1188096, 175921860575488,
    93458759024896, 18691832414208, 405274624, 250688786931712, 175930788020224, 18700355772416,
    74775447732224, 2164396320, 9418863411456, 309237776640, 309372387328, 9348147838976,
    73149190176, 81671487488, 9663743528992, 10821304320, 2165350545, 73014476928, 309508210816,
    309237645329, 2434793472, 73015500800, 73318596625, 309272322048, 2197880832, 37024,
    2336462241920, 74766790721664, 77103252901920, 2336495828992, 33624096, 74766824308736,
    4243584, 185268791443584, 18709414445184, 18692779802624, 9363565576192, 175921864654848,
    175939610804224, 28037584338944, 1115750400]

set_option maxHeartbeats 0 in
theorem roots_closed : rootsClosed (rootsOf ()) = true := by
  decide +kernel

theorem all_of_chunks {α : Type} (f : α → Bool) (c : Nat) :
    ∀ (m : Nat) (L : List α), L.length ≤ m * c →
      (∀ j < m, ((L.drop (j * c)).take c).all f = true) → L.all f = true
  | 0, L, hL, _ => by
    simp at hL
    simp [hL]
  | m + 1, L, hL, h => by
    rw [← List.take_append_drop c L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_chunks f c m (L.drop c) ?_ fun j hj => ?_⟩
    · rw [List.length_drop]
      rw [Nat.succ_mul] at hL
      omega
    · have h' := h (j + 1) (by omega)
      have e : L.drop ((j + 1) * c) = (L.drop c).drop (j * c) := by
        simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]
      rwa [e] at h'

@[expose] def coverRow (c₁ : Array Nat) : Bool :=
  vecs.all fun c₂ => !indep c₁ c₂ || keyCodes.any fun m => Nat.beq m (encodeB (key (rootsOf ()) c₁ c₂))

set_option maxHeartbeats 0 in
theorem cover_chunk_0 : ((vecs.drop (0 * 9)).take 9).all coverRow = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_chunk_1 : ((vecs.drop (1 * 9)).take 9).all coverRow = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_chunk_2 : ((vecs.drop (2 * 9)).take 9).all coverRow = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_chunk_3 : ((vecs.drop (3 * 9)).take 9).all coverRow = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_chunk_4 : ((vecs.drop (4 * 9)).take 9).all coverRow = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_chunk_5 : ((vecs.drop (5 * 9)).take 9).all coverRow = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_chunk_6 : ((vecs.drop (6 * 9)).take 9).all coverRow = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_chunk_7 : ((vecs.drop (7 * 9)).take 9).all coverRow = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_chunk_8 : ((vecs.drop (8 * 9)).take 9).all coverRow = true := by
  decide +kernel

theorem keys_cover : (vecs.all fun c₁ => vecs.all fun c₂ =>
    !indep c₁ c₂ || keyCodes.any fun m => Nat.beq m (encodeB (key (rootsOf ()) c₁ c₂))) = true := by
  refine all_of_chunks coverRow 9 9 vecs (by decide) fun j hj => ?_
  match j, hj with
  | 0, _ => exact cover_chunk_0
  | 1, _ => exact cover_chunk_1
  | 2, _ => exact cover_chunk_2
  | 3, _ => exact cover_chunk_3
  | 4, _ => exact cover_chunk_4
  | 5, _ => exact cover_chunk_5
  | 6, _ => exact cover_chunk_6
  | 7, _ => exact cover_chunk_7
  | 8, _ => exact cover_chunk_8
  | j + 9, h => exact absurd h (by omega)

set_option maxHeartbeats 0 in
theorem keys_ok : keyCodes.all (fun m => G (rootsOf ()) (decodeB (rootsOf ()).length m)) = true := by
  decide +kernel

private theorem a3_f4_check_0 : check () = true := by
  show (rootsClosed (rootsOf ()) && mainCheck (rootsOf ())) = true
  rw [roots_closed, mainCheck_of _ keyCodes keys_cover keys_ok]
  rfl

end CertificateChecks.Batch715501

namespace Certificates

open Certificates.A3LatticeF4 in
theorem certificate715501 : check () = true := by
  exact CertificateChecks.Batch715501.a3_f4_check_0

end Certificates
