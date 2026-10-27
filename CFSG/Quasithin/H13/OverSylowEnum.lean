module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.LocDblDcos

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.Dc

variable {Γ : Type} [Group Γ]

theorem enum_spec [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ p ∈ B, act n g p = p) → g = 1)
    (G : Array (Array ℕ)) (L : List Γ) (hlen : L.length = G.size)
    (hG : ∀ t < G.size, ∀ p < n, img (G.getD t #[]) p = act n (L.getD t 1) p)
    (par lab : Array ℕ) (N : ℕ) (hok : enumOK N G par lab = true)
    (hd : distinctNat (rowKeys n B G par lab N) = true) (hcl : closedOK n B G par lab N = true)
    (hN : 0 < N) :
    Nat.card (Subgroup.closure {x | x ∈ L}) = N ∧
      ∀ g : Γ, g ∈ Subgroup.closure {x | x ∈ L} ↔
        ∃ k < N, (B.map (ptsArr G par lab N)).map (fun A => A.getD k 0) = B.map (act n g) := by
  have hkeys := rowKeys_eq hB G L par lab N hG hok
  have hinj := inj_of_nodup (hkeys ▸ distinctNat_nodup hd)
  have hclosed := closed_of_closedOK hB hbase G L hlen par lab N hG hok hcl
  obtain ⟨hsurj, hcard⟩ := enum_closure L (enumElt L par lab) N hN (enumElt_zero _ _ _)
    (enumElt_mem _ _ _) hinj hclosed
  refine ⟨hcard, fun g => ⟨fun hg => ?_, fun ⟨k, hk, hrow⟩ => ?_⟩⟩
  · obtain ⟨k, hk, rfl⟩ := hsurj g hg
    exact ⟨k, hk, rows_spec hB G L par lab N hG hok hk⟩
  · have h := rows_spec hB G L par lab N hG hok hk
    have hmap : B.map (act n (enumElt L par lab k)) = B.map (act n g) := h.symm.trans hrow
    have heq : enumElt L par lab k = g :=
      eq_of_base hB hbase fun p hp => (List.map_inj_left.mp hmap) p hp
    exact heq ▸ enumElt_mem L par lab k

end CFSG.Quasithin.H13.LocDbl
