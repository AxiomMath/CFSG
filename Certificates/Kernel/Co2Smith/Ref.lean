module

public import Certificates.Kernel.Co2Smith.Elem
public import Certificates.Kernel.Co2Smith.RefRowK
public import Certificates.Kernel.Co2Smith.RefImgK
public import Certificates.Kernel.Co2Smith.RefClsK
public import Certificates.Kernel.Sporadic.Co2.Order
public import CFSG.Certificates.Kernel.Co2Smith.RefineASound
public import CFSG.Sporadic.Co2Smith.GlRefineFacts
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.Co2SmithR CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.Co2Cert
open CertificateChecks.KernelSpor

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem memA_spec {l : List Nat} {v : Nat} (h : memA l v = true) : v ∈ l := by
  induction l with
  | nil => exact absurd h (by simp [memA])
  | cons a l ih =>
    by_cases e : a = v
    · subst e
      exact List.mem_cons_self
    · have h' : memA l v = true := by
        have hb : Nat.beq a v = false := by
          cases hh : Nat.beq a v
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hh) e
        simpa [memA, hb] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem co2P_le : co2P ≤ Subgroup.closure
    (Set.range fun j : Fin 2 => permOfArr 2300 (unpack 2300 12 (Co2A.S j.val))) := by
  unfold co2P
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure ⟨0, by rw [co2Gen, Co2Order.a_eq 0 (by norm_num)]; rfl⟩
  · exact Subgroup.subset_closure ⟨1, by rw [co2Gen, Co2Order.a_eq 1 (by norm_num)]; rfl⟩

theorem arc_comm {P : Nat} (hP : ∀ y < 2300, pg 12 4095 P y < 2300) {σ : Equiv.Perm (Fin 2300)}
    (h : ArcComm σ (unpack 2300 12 P)) (y z : Fin 2300) (hz : (z : ℕ) = pg 12 4095 P y) :
    ((σ z : Fin 2300) : ℕ) = pg 12 4095 P (σ y) := by
  obtain ⟨A, hA, -⟩ := h.2
  have e1 := ArcComm.apply h hA y
  rw [unpack12 (σ y).2] at e1
  have e2 : z = A y := by
    apply Fin.ext
    rw [hz, ← hA y, unpack12 y.2]
  rw [e1, e2]

theorem arcs_lt : ∀ j < 3, ∀ y < 2300, pg 12 4095 (AP j) y < 2300 := by
  have h := arc_k
  unfold arcK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro j hj y hy
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact (bind_facts h1 hy).1
  · exact (bind_facts h2 hy).1
  · exact (bind_facts h3 hy).1

theorem arcs_eq : glPermArr glAl = unpack 2300 12 (AP 0) ∧ glPermArr glGa = unpack 2300 12 (AP 1) ∧
    glPermArr glZ = unpack 2300 12 (AP 2) := by
  have h := arc_k
  unfold arcK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by rw [glAl_eq]; exact permArr_eq h1, by rw [glGa_eq]; exact permArr_eq h2, ?_⟩
  rw [glZ_eq]
  exact permArr_eq h3

theorem gens_perm : ∀ j < 2, CFSG.KC.Misc.ArrEnum.permB 2300 12 (Co2A.S j) = true := by
  intro j hj
  have := CFSG.KS.allN_spec strong_permB j (by omega)
  simp only [Bool.and_eq_true] at this
  exact this.1

theorem colour_inv {js pre : List Nat} (hjs : ∀ j ∈ js, j < 3) (hsm : 2 ^ js.length * (pre.length + 1) ≤ 2 ^ 31)
    {σ : Equiv.Perm (Fin 2300)} (hσ : σ ∈ co2P)
    (harc : ∀ j ∈ js, ArcComm σ (unpack 2300 12 (AP j)))
    (hpre : ∀ v : Fin 2300, (v : ℕ) ∈ pre → σ v = v) :
    ∀ v : Fin 2300, cgA (colourA 2300 RS (js.map AP) pre 3) (σ v) =
      cgA (colourA 2300 RS (js.map AP) pre 3) v := by
  refine colourA_inv (d := 891) (ng := 2) (R := RR) (M := RM) (G := Co2A.S) (by norm_num)
    (by norm_num) rows_ok (fun j hj x hx => ?_) gens_perm ?_ (by simpa using hsm) (co2P_le hσ) ?_
    hpre
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact img0_ok x hx
    · exact img1_ok x hx
  · intro T hT y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hT
    exact arcs_lt j (hjs j hj) y hy
  · intro T hT y z hz
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hT
    exact arc_comm (arcs_lt j (hjs j hj)) (harc j hj) y z hz

theorem mem_of_classA {Ts pre pts : List Nat} {x : Nat} (hc : classA 2300 RS Ts pre 3 x pts = true)
    (hx : x < 2300) {σ : Equiv.Perm (Fin 2300)}
    (hinv : ∀ v : Fin 2300, cgA (colourA 2300 RS Ts pre 3) (σ v) = cgA (colourA 2300 RS Ts pre 3) v) :
    ((σ ⟨x, hx⟩ : Fin 2300) : ℕ) ∈ pts := by
  unfold classA at hc
  rw [strictB_eq'] at hc
  have h := CFSG.KS.allN_spec hc _ (σ ⟨x, hx⟩).2
  have hb : Nat.beq (cgA (colourA 2300 RS Ts pre 3) (σ ⟨x, hx⟩))
      (cgA (colourA 2300 RS Ts pre 3) x) = true := by
    rw [hinv ⟨x, hx⟩]
    exact Nat.beq_refl _
  rw [hb] at h
  exact memA_spec h

theorem fix_of_singA {Ts pre : List Nat}
    (hs : ∀ b < 9, singA 2300 RS Ts pre 3 (256 * b) (if b = 8 then 252 else 256) = true)
    {σ : Equiv.Perm (Fin 2300)}
    (hinv : ∀ v : Fin 2300, cgA (colourA 2300 RS Ts pre 3) (σ v) = cgA (colourA 2300 RS Ts pre 3) v) :
    σ = 1 := by
  refine Equiv.ext fun v => Fin.ext ?_
  have hb : v.val / 256 < 9 := by omega
  have h := hs _ hb
  unfold singA at h
  rw [strictB_eq'] at h
  have hi : v.val % 256 < (if v.val / 256 = 8 then 252 else 256) := by
    split_ifs <;> omega
  have h2 := CFSG.KS.allN_spec h _ hi
  have ev : Nat.add (256 * (v.val / 256)) (v.val % 256) = v.val := Nat.div_add_mod _ _
  rw [ev, strictB_eq'] at h2
  have h3 := CFSG.KS.allN_spec h2 _ (σ v).2
  have hb' : Nat.beq (cgA (colourA 2300 RS Ts pre 3) (σ v))
      (cgA (colourA 2300 RS Ts pre 3) v.val) = true := by
    rw [hinv v]
    exact Nat.beq_refl _
  rw [hb'] at h3
  exact Nat.eq_of_beq_eq_true h3

theorem c0_sing : ∀ b < 9, singA 2300 RS c0Arcs [80, 1, 0] 3 (256 * b)
    (if b = 8 then 252 else 256) = true := by
  intro b hb
  interval_cases b
  exacts [c0_sing0, c0_sing1, c0_sing2, c0_sing3, c0_sing4, c0_sing5, c0_sing6, c0_sing7, c0_sing8]

theorem cz_sing : ∀ b < 9, singA 2300 RS czArcs [80, 1, 0] 3 (256 * b)
    (if b = 8 then 252 else 256) = true := by
  intro b hb
  interval_cases b
  exacts [cz_sing0, cz_sing1, cz_sing2, cz_sing3, cz_sing4, cz_sing5, cz_sing6, cz_sing7, cz_sing8]

theorem pre_fix {σ : Equiv.Perm (Fin 2300)} {pre : List Nat}
    (h : ∀ x ∈ pre, ∀ hx : x < 2300, σ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ v : Fin 2300, (v : ℕ) ∈ pre → σ v = v := fun v hv => h v.val hv v.2

theorem refC0_facts : GlOrbitFacts [glPermArr glAl, glPermArr glGa] (glWit0.map (·.1))
    (glWit1.map (·.1)) (glWit2.map (·.1)) [(1172, glWit0Pts 1), (1348, glWit0Pts 2)] := by
  obtain ⟨eA, eG, -⟩ := arcs_eq
  have hjs : ∀ j ∈ [0, 1], j < 3 := by decide
  have harc : ∀ σ : Equiv.Perm (Fin 2300), (∀ p ∈ [glPermArr glAl, glPermArr glGa], ArcComm σ p) →
      ∀ j ∈ [0, 1], ArcComm σ (unpack 2300 12 (AP j)) := by
    intro σ h j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · rw [← eA]; exact h _ List.mem_cons_self
    · rw [List.mem_singleton.1 hj, ← eG]
      exact h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hmap : c0Arcs = [0, 1].map AP := rfl
  refine ⟨fun σ hσ ha => ?_, fun σ hσ ha h80 => ?_, fun σ hσ ha h80 e he hx => ?_,
    fun σ hσ ha h80 h1 => ?_, fun σ hσ ha h80 h1 h0 => ?_⟩
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := []) (fun v hv => by simp at hv)
    rw [← hmap] at hinv
    have := mem_of_classA c0_cls0 (by norm_num) hinv
    exact this
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := [80]) (pre_fix fun x hx hx' => by
      obtain rfl := List.mem_singleton.1 hx; exact h80)
    rw [← hmap] at hinv
    have := mem_of_classA c0_cls1 (by norm_num) hinv
    exact this
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := [80]) (pre_fix fun x hx hx' => by
      obtain rfl := List.mem_singleton.1 hx; exact h80)
    rw [← hmap] at hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact mem_of_classA c0_extra1 hx hinv
    · exact mem_of_classA c0_extra2 hx hinv
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := [80, 1])
      (pre_fix fun x hx hx' => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h80
        · obtain rfl := List.mem_singleton.1 hx; exact h1)
    rw [← hmap] at hinv
    have := mem_of_classA c0_cls2 (by norm_num) hinv
    exact this
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := [80, 1, 0])
      (pre_fix fun x hx hx' => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h80
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1
        · obtain rfl := List.mem_singleton.1 hx; exact h0)
    rw [← hmap] at hinv
    exact fix_of_singA c0_sing hinv

theorem refCz_facts : GlOrbitFacts [glPermArr glAl, glPermArr glGa, glPermArr glZ]
    (glWitZ0.map (·.1)) (glWitZ1.map (·.1)) (glWitZ2.map (·.1)) [] := by
  obtain ⟨eA, eG, eZ⟩ := arcs_eq
  have hjs : ∀ j ∈ [0, 1, 2], j < 3 := by decide
  have harc : ∀ σ : Equiv.Perm (Fin 2300),
      (∀ p ∈ [glPermArr glAl, glPermArr glGa, glPermArr glZ], ArcComm σ p) →
      ∀ j ∈ [0, 1, 2], ArcComm σ (unpack 2300 12 (AP j)) := by
    intro σ h j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · rw [← eA]; exact h _ List.mem_cons_self
    rcases List.mem_cons.1 hj with rfl | hj
    · rw [← eG]; exact h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [List.mem_singleton.1 hj, ← eZ]
      exact h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hmap : czArcs = [0, 1, 2].map AP := rfl
  refine ⟨fun σ hσ ha => ?_, fun σ hσ ha h80 => ?_, fun σ hσ ha h80 e he hx => absurd he (by simp),
    fun σ hσ ha h80 h1 => ?_, fun σ hσ ha h80 h1 h0 => ?_⟩
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := []) (fun v hv => by simp at hv)
    rw [← hmap] at hinv
    have := mem_of_classA cz_cls0 (by norm_num) hinv
    exact this
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := [80]) (pre_fix fun x hx hx' => by
      obtain rfl := List.mem_singleton.1 hx; exact h80)
    rw [← hmap] at hinv
    have := mem_of_classA cz_cls1 (by norm_num) hinv
    exact this
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := [80, 1])
      (pre_fix fun x hx hx' => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h80
        · obtain rfl := List.mem_singleton.1 hx; exact h1)
    rw [← hmap] at hinv
    have := mem_of_classA cz_cls2 (by norm_num) hinv
    exact this
  · have hinv := colour_inv hjs (by norm_num) hσ (harc σ ha) (pre := [80, 1, 0])
      (pre_fix fun x hx hx' => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h80
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1
        · obtain rfl := List.mem_singleton.1 hx; exact h0)
    rw [← hmap] at hinv
    exact fix_of_singA cz_sing hinv

end CertificateChecks.KernelCo2Smith

end
