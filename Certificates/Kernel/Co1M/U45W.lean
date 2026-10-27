module

public import Certificates.Kernel.Co1M.C73
public import Certificates.Kernel.Co1M.K45S0
public import Certificates.Kernel.Co1M.K45S1
public import Certificates.Kernel.Co1M.K45S2
public import Certificates.Kernel.Co1M.K45E
public import Certificates.Kernel.Co1M.K39E
public import CFSG.Monster.GMS.S365UKInputs
public import CFSG.Certificates.Kernel.Co1M.U45Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.SortTree CFSG.KC.U45 CFSG.KD.Co1M CFSG.Sporadic.Co1.Module.Odd

@[expose] noncomputable def u45 : UW := ⟨SI45, SE45, CE45⟩

@[expose] noncomputable def u39 : UW := ⟨SI45, SE39, CE39⟩

theorem u45_lt {a b c : ℕ} (h : a < b) (e : b = c) : a < c := e ▸ h

theorem u45_slices : ∀ q < 179, st45S q = true := by
  intro q hq
  by_cases h0 : q < 60
  · exact ST45x0.all q h0
  have e : ∀ a, a ≤ q → Nat.add a (q - a) = q := fun a ha => by
    change a + (q - a) = q
    omega
  by_cases h1 : q < 120
  · have := ST45x1.all (q - 60) (u45_lt (b := 60) (by omega) rfl)
    unfold st45F1 at this
    rwa [e 60 (by omega)] at this
  · have := ST45x2.all (q - 120) (u45_lt (b := 59) (by omega) rfl)
    unfold st45F2 at this
    rwa [e 120 (by omega)] at this

theorem u45_st : ∀ i < nS, stRec w73.T.wl w73.T.wp w73.T.tab SI45 i = true := by
  intro i hi
  obtain ⟨hq, e, hm⟩ := split_idx (n := nS) (B := 1024) (C := 179) (by decide) hi
  have h := u45_slices _ hq
  unfold st45S stRun at h
  have hj : i % 1024 < cntF 182919 1024 (i / 1024 * 1024) := by
    rw [cntF_eq]
    have : i < 182919 := hi
    omega
  have h' := (allN_iff _ _).1 h (i % 1024) hj
  simp only [Nat.add_eq, Nat.mul_eq, e] at h'
  exact h'

theorem u45_t4 {nw : ℕ} {L : List (List ℕ)} (h : t45K nw L = true) :
    ∀ e ∈ L, type4U (getL 0 e 2) = true ∧ type4U (getL 0 e (lastO nw)) = true := by
  intro e he
  have h' := (allE_iff _ _).1 h e he
  rw [andB45] at h'
  unfold type4U
  rw [CertificateChecks.KernelCo1M.c73_t4, CertificateChecks.KernelCo1M.c73_t4]
  exact h'

theorem u45_t4L {nw : ℕ} {L M : List (List ℕ)} (hL : t45K nw L = true) (hM : t45K nw M = true) :
    ∀ e ∈ L ++ M, type4U (getL 0 e 2) = true ∧ type4U (getL 0 e (lastO nw)) = true := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact u45_t4 hL e he
  · exact u45_t4 hM e he

theorem u45_hd {SE CE : List (List ℕ)} (h : hd45K SE CE = true) :
    eqL (headsE SE) SI45 = true ∧ incE CE 0 = true ∧ lenE CE = 759 := by
  unfold hd45K at h
  rw [andB45, andB45, beq_iff] at h
  exact h

theorem u45_ok : UOK w73 1 u45 where
  nw1 := le_rfl
  st := u45_st
  heads := (u45_hd k45_hd).1
  se := k45_se
  ce := k45_ce
  cinc := (u45_hd k45_hd).2.1
  clen := (u45_hd k45_hd).2.2
  t4 := u45_t4L k45_t4s k45_t4c

theorem u39_ok : UOK w73 2 u39 where
  nw1 := by norm_num
  st := u45_st
  heads := (u45_hd k39_hd).1
  se := k39_se
  ce := k39_ce
  cinc := (u45_hd k39_hd).2.1
  clen := (u45_hd k39_hd).2.2
  t4 := u45_t4L k39_t4s k39_t4c

end CertificateChecks.KernelCo1M

end
