
module

public import CFSG.GH74.KGroups.L34TablesBase
public import CFSG.GH74.Uniqueness.SU.KI1r4L34ModelInputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K5140
import Certificates.Kernel.PermCent.K5140Side
public import Certificates.Data.Kernel.PermCent.CV

@[expose] public section

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L34Mod
  CFSG.Certificates.Kernel.PkEnum

local notation "Pm" => Equiv.Perm (Fin 42)

namespace CertificateChecks.Batch5140

private theorem cOf_injective : Function.Injective (cOf : Pm → CV 42) := fun a b h => by
  rw [← ev_cOf a, h, ev_cOf]

private theorem cOf_mul (a b : Pm) : cOf (a * b) = cOf a * cOf b :=
  ev_injective (by rw [ev_mul, ev_cOf, ev_cOf, ev_cOf])

private theorem cOf_inv (a : Pm) : cOf a⁻¹ = (cOf a)⁻¹ :=
  ev_injective (by rw [ev_inv, ev_cOf, ev_cOf])

private theorem cOf_one' : cOf (1 : Pm) = 1 := ev_injective (by rw [ev_cOf, ev_one])

private theorem foldl_inv {α β : Type*} (p : α → Prop) (f : List α → β → List α) :
    ∀ (L : List β) (acc : List α), (∀ acc, ∀ b ∈ L, (∀ x ∈ acc, p x) → ∀ x ∈ f acc b, p x) →
      (∀ x ∈ acc, p x) → ∀ x ∈ L.foldl f acc, p x
  | [], _, _, h => h
  | b :: L, acc, hf, h =>
    foldl_inv p f L (f acc b) (fun acc b' hb' => hf acc b' (List.mem_cons_of_mem _ hb'))
      (hf acc b (by simp) h)

private theorem bfs_mem (gens : List Pm) (H : Subgroup Pm) (hg : ∀ s ∈ gens, s ∈ H) :
    ∀ (n : ℕ) (seen front : List Pm), (∀ x ∈ seen, x ∈ H) → (∀ x ∈ front, x ∈ H) →
      ∀ x ∈ bfsClosure gens n seen front, x ∈ H
  | 0, seen, front, hs, _ => by
    simp only [bfsClosure]
    exact hs
  | _ + 1, seen, [], hs, _ => by
    simp only [bfsClosure]
    exact hs
  | n + 1, seen, g :: rest, hs, hf => by
    simp only [bfsClosure]
    have hgH : g ∈ H := hf g (by simp)
    have hnew := foldl_inv (· ∈ H) (fun acc s => if tab (g * s) ∈ seen ∨ tab (g * s) ∈ acc then
        acc else acc ++ [tab (g * s)]) gens [] (fun acc s hs' hacc x hx => by
          split_ifs at hx with hc
          · exact hacc x hx
          · rcases List.mem_append.1 hx with hx | hx
            · exact hacc x hx
            · rw [List.mem_singleton.1 hx, tab_eq]
              exact H.mul_mem hgH (hg s hs')) (by simp)
    apply bfs_mem gens H hg n
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hs x hx
      · exact hnew x hx
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hf x (List.mem_cons_of_mem _ hx)
      · exact hnew x hx

private theorem foldl_map (g : Pm) (seen : List Pm) : ∀ (L acc : List Pm),
    (L.foldl (fun acc s => if tab (g * s) ∈ seen ∨ tab (g * s) ∈ acc then acc
      else acc ++ [tab (g * s)]) acc).map cOf =
    (L.map cOf).foldl (fun acc s => if cOf g * s ∈ seen.map cOf ∨ cOf g * s ∈ acc then acc
      else acc ++ [cOf g * s]) (acc.map cOf)
  | [], _ => rfl
  | s :: L, acc => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, foldl_map g seen L]
    congr 1
    have e : (cOf g * cOf s ∈ seen.map cOf ∨ cOf g * cOf s ∈ acc.map cOf) ↔
        (g * s ∈ seen ∨ g * s ∈ acc) := by
      rw [← cOf_mul, List.mem_map_of_injective cOf_injective,
        List.mem_map_of_injective cOf_injective]
    simp only [tab_eq]
    by_cases hc : g * s ∈ seen ∨ g * s ∈ acc
    · rw [if_pos hc, if_pos (e.2 hc)]
    · rw [if_neg hc, if_neg (mt e.1 hc), List.map_append, List.map_singleton, cOf_mul]

private theorem bfs_map (gens : List Pm) : ∀ (n : ℕ) (seen front : List Pm),
    (bfsClosure gens n seen front).map cOf = bfsC (gens.map cOf) n (seen.map cOf) (front.map cOf)
  | 0, seen, front => by simp only [bfsClosure, bfsC]
  | _ + 1, seen, [] => by simp only [bfsClosure, bfsC, List.map_nil]
  | n + 1, seen, g :: rest => by
    simp only [bfsClosure, bfsC, List.map_cons]
    rw [bfs_map gens n, List.map_append, List.map_append, foldl_map, List.map_nil]

private theorem s0_map : s0list.map cOf = sC := by
  unfold s0list sC gS
  rw [bfs_map, List.map_singleton, cOf_one']

end CertificateChecks.Batch5140

namespace Certificates

open CertificateChecks.Batch5140

end Certificates
