module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23CheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Orb
import Certificates.Kernel.LocalQT.Insp.C4088a
import Certificates.Kernel.LocalQT.Insp.C4088b
import Certificates.Kernel.LocalQT.Insp.C4088g
import Certificates.Data.Kernel.LocalQT.Insp
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.Certificates.Kernel.LocalQTSyl24Sound
import CFSG.Certificates.Kernel.LocalQTSylSound

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.M23Insp
open scoped Pointwise
open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

private theorem chk_card :
    data.B₀.card = 7 := by
  decide +kernel

private theorem chk_H_reach :
    Reach data.gens data.B₀ data.H data.hp data.hl := by
  decide +kernel

private theorem chk_H_closed :
    ClosedUnder data.gens data.H := CFSG.KD.LQT.C4088.H_closed

private theorem chk_H_nodup :
    data.H.Nodup := CFSG.KD.LQT.C4088.H_nodup

private theorem chk_ks_fix :
    ∀ g ∈ data.ks, g • data.B₀ = data.B₀ := by
  decide +kernel

private theorem chk_R₁_reach :
    Reach data.ks data.r₁ data.R₁ data.p₁ data.l₁ := by
  decide +kernel

private theorem chk_R₂_reach :
    Reach data.ks data.r₂ data.R₂ data.p₂ data.l₂ := by
  decide +kernel

private theorem chk_R₁_nodup :
    data.R₁.Nodup := by
  decide +kernel

private theorem chk_R₂_nodup :
    data.R₂.Nodup := by
  decide +kernel

private theorem chk_R₁_sub :
    AllMem data.R₁ (fun B => B ∈ data.H) := by
  decide +kernel

private theorem chk_R₂_sub :
    AllMem data.R₂ (fun B => B ∈ data.H) := by
  decide +kernel

private theorem chk_B₀_not₁ :
    data.B₀ ∉ data.R₁ := by
  decide +kernel

private theorem chk_B₀_not₂ :
    data.B₀ ∉ data.R₂ := by
  decide +kernel

private theorem chk_cover :
    AllMem data.H (fun B => B ≠ data.B₀ → B ∈ data.R₁ ∨ B ∈ data.R₂) :=
  CFSG.KD.LQT.C4088.cover

private theorem chk_lev₁ :
    AllMem data.H
        (fun B => B ≠ data.B₀ → (B ∈ data.R₁ ↔ (B ∩ data.B₀).card = data.c₁)) :=
  CFSG.KD.LQT.C4088.lev₁

private theorem chk_lev₂ :
    AllMem data.H
        (fun B => B ≠ data.B₀ → (B ∈ data.R₂ ↔ (B ∩ data.B₀).card = data.c₂)) :=
  CFSG.KD.LQT.C4088.lev₂

private theorem chk_harith :
    ∀ k ∈ List.range data.H.length, k ∣ data.H.length →
        k < 1 + data.R₁.length ∧ k < 1 + data.R₂.length := by
  decide +kernel

private theorem chk_T_reach :
    Reach data.ks data.t₀ data.T data.tp data.tl := CFSG.KD.LQT.C4088.T_reach

private theorem chk_T_nodup_map :
    (data.T.map enc).Nodup := CFSG.KD.LQT.C4088.T_nodup

private theorem chk_t₀_mem :
    ∀ i, data.t₀ i ∈ data.B₀ := by
  decide +kernel

private theorem chk_Es_len :
    data.Es.length = 16 := by
  decide +kernel

private theorem chk_Es_nodup :
    data.Es.Nodup := by
  decide +kernel

private theorem chk_Es_fix :
    ∀ e ∈ data.Es, ∀ x ∈ data.B₀, e • x = x := by
  decide +kernel

private theorem chk_Es_sq :
    ∀ e ∈ data.Es, e * e = 1 := by
  decide +kernel

private theorem chk_Es_comm :
    ∀ e ∈ data.Es, ∀ f ∈ data.Es, e * f = f * e := CFSG.KD.LQT.C4088.Es_comm

private theorem chk_noncentral :
    ∃ k ∈ data.ks, ∃ e ∈ data.Es, k * e ≠ e * k := by
  decide +kernel

private theorem chk_T_len :
    data.T.length * 2 = Nat.factorial 7 := by
  decide +kernel

private theorem chk_num_M :
    data.H.length * (16 * data.T.length) = 2 ^ data.e * data.u := by
  decide +kernel

private theorem chk_num_K :
    16 * data.T.length = 2 ^ data.e * data.u' := by
  decide +kernel

private theorem chk_div₁ :
    ¬ 2 ^ data.e ∣ (2 ^ data.e * data.u') / data.R₁.length := by
  decide +kernel

private theorem chk_div₂ :
    ¬ 2 ^ data.e ∣ (2 ^ data.e * data.u') / data.R₂.length := by
  decide +kernel

private theorem chk_H_len :
    data.H.length = 253 := by
  decide +kernel

private theorem chk_T_len' :
    data.T.length = 2520 := by
  decide +kernel

end CFSG.QuasithinUnique.Vol2Native.L239.M23Insp

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M23Insp in
open scoped Pointwise in
open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 in
theorem certificate4088 : (data.B₀.card = 7)
    ∧ (Reach data.gens data.B₀ data.H data.hp data.hl)
    ∧ (ClosedUnder data.gens data.H)
    ∧ (data.H.Nodup)
    ∧ (∀ g ∈ data.ks, g • data.B₀ = data.B₀)
    ∧ (Reach data.ks data.r₁ data.R₁ data.p₁ data.l₁)
    ∧ (Reach data.ks data.r₂ data.R₂ data.p₂ data.l₂)
    ∧ (data.R₁.Nodup)
    ∧ (data.R₂.Nodup)
    ∧ (AllMem data.R₁ (fun B => B ∈ data.H))
    ∧ (AllMem data.R₂ (fun B => B ∈ data.H))
    ∧ (data.B₀ ∉ data.R₁)
    ∧ (data.B₀ ∉ data.R₂)
    ∧ (AllMem data.H (fun B => B ≠ data.B₀ → B ∈ data.R₁ ∨ B ∈ data.R₂))
    ∧ (AllMem data.H
          (fun B => B ≠ data.B₀ → (B ∈ data.R₁ ↔ (B ∩ data.B₀).card = data.c₁)))
    ∧ (AllMem data.H
          (fun B => B ≠ data.B₀ → (B ∈ data.R₂ ↔ (B ∩ data.B₀).card = data.c₂)))
    ∧ (∀ k ∈ List.range data.H.length, k ∣ data.H.length →
          k < 1 + data.R₁.length ∧ k < 1 + data.R₂.length)
    ∧ (Reach data.ks data.t₀ data.T data.tp data.tl)
    ∧ ((data.T.map CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.enc).Nodup)
    ∧ (∀ i, data.t₀ i ∈ data.B₀)
    ∧ (data.Es.length = 16)
    ∧ (data.Es.Nodup)
    ∧ (∀ e ∈ data.Es, ∀ x ∈ data.B₀, e • x = x)
    ∧ (∀ e ∈ data.Es, e * e = 1)
    ∧ (∀ e ∈ data.Es, ∀ f ∈ data.Es, e * f = f * e)
    ∧ (∃ k ∈ data.ks, ∃ e ∈ data.Es, k * e ≠ e * k)
    ∧ (data.T.length * 2 = Nat.factorial 7)
    ∧ (data.H.length * (16 * data.T.length) = 2 ^ data.e * data.u)
    ∧ (16 * data.T.length = 2 ^ data.e * data.u')
    ∧ (¬ 2 ^ data.e ∣ (2 ^ data.e * data.u') / data.R₁.length)
    ∧ (¬ 2 ^ data.e ∣ (2 ^ data.e * data.u') / data.R₂.length)
    ∧ (data.H.length = 253)
    ∧ (data.T.length = 2520) :=
  ⟨CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_card,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_H_reach,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_H_closed,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_H_nodup,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_ks_fix,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_R₁_reach,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_R₂_reach,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_R₁_nodup,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_R₂_nodup,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_R₁_sub,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_R₂_sub,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_B₀_not₁,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_B₀_not₂,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_cover,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_lev₁,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_lev₂,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_harith,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_T_reach,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_T_nodup_map,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_t₀_mem,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_Es_len,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_Es_nodup,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_Es_fix,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_Es_sq,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_Es_comm,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_noncentral,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_T_len,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_num_M,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_num_K,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_div₁,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_div₂,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_H_len,
    CFSG.QuasithinUnique.Vol2Native.L239.M23Insp.chk_T_len'⟩

end Certificates
