module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24TGen
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24TCentSets
public import CFSG.Open.QuasithinDefs
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24T
public import CFSG.Monster.B.Co2.IrredAllBase
public import CFSG.Monster.B.Co2.IrredBase
public import CFSG.Monster.B.Co2.IrredMainBase
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Co2Inv.CentOrderBase
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertBase
public import CFSG.Monster.B.TwoA.Co2Inv.MrBase
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import Certificates.Certificate3055Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.Fischer CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] rAction

local notation "bP" => @famProd R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm

section Z


@[expose] noncomputable def fi24z : CFSG.Sporadic.Fi24.J := fi24EOf {0, 3, 13, 15} (by decide)

theorem jR_fi24z : jR fi24z = bP {0, 3, 13, 15} := jR_fi24EOf _ _

theorem fi24z_mem : fi24z ∈ fi24E := fi24EOf_mem _ _

end Z

section Sig


@[expose] noncomputable def fi24Sig (k : Fin 4) : Equiv.Perm (Fin 24) :=
  fi24EC * (m24Sg[k.val]'(k.isLt.trans_eq length_m24Sg.symm) : Equiv.Perm (Fin 24)) * fi24EC⁻¹

theorem fi24Sig_val (k : Fin 4) (i : Fin 24) : (fi24Sig k i).val = (fi24ESb[k.val]!)[i.val]! :=
  (fi24ESb_eq _ i).symm

end Sig

section Cent


theorem bbarProd_small {S : Finset (Fin 24)} (hS : S.card ≤ 6) (h : bP S = 1) : S = ∅ :=
  eq_of_bbarProd_eq (by rwa [← Finset.bot_eq_empty, symmDiff_bot])
    (h.trans bbarProd_empty.symm)


theorem bbarProd_fi24Sig {t : CFSG.Sporadic.Fi24.J} (hc : ∀ s ∈ fi24T, s * t = t * s) {U : Finset (Fin 24)}
    (hU : jR t = bP U) (k : Fin 4) : bP (U.map (fi24Sig k).toEmbedding) = bP U := by
  obtain ⟨n, hnT, hn⟩ :=
    exists_fi24T_of_mem (List.getElem_mem (k.isLt.trans_eq length_m24Sg.symm))
  have h2 := jR_conj_eq (n := n) hU
  rw [hc _ hnT, mul_inv_cancel_right, hU, hn] at h2
  exact h2.symm

theorem conj_fi24z {n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)} {k : ℕ} (hk : k < m24Sg.length)
    (hn : fi24Pi n = fi24EC * (m24Sg[k] : Equiv.Perm (Fin 24)) * fi24EC⁻¹) :
    (n : CFSG.Sporadic.Fi24.J) * fi24z * (n : CFSG.Sporadic.Fi24.J)⁻¹ = fi24z := by
  have e := @famProd_Z0 R inferInstance bbar bbar_comm bbar_sq fi24Sig fi24Sig_val
    (fun _ hO => bbarProd_octad hO) ⟨k, hk.trans_eq length_m24Sg⟩
  apply jR_injective
  rw [jR_conj_eq jR_fi24z, jR_fi24z, hn]
  exact e

theorem comm_fi24z {s : CFSG.Sporadic.Fi24.J} (hs : s ∈ fi24T) : s * fi24z = fi24z * s := by
  let C : Subgroup (normalizer (fi24E : Set J)) :=
    (centralizer {fi24z}).comap (normalizer (fi24E : Set J)).subtype
  have hker : fi24Pi.ker ≤ C := fun n hn => by
    have hnE : (n : J) ∈ fi24E := fi24Pi_eq_one_iff.1 (MonoidHom.mem_ker.1 hn)
    change (n : J) ∈ centralizer {fi24z}
    rw [mem_centralizer_singleton_iff]
    apply jR_injective
    rw [map_mul, map_mul]
    exact fi24EB_mul_comm (mem_fi24E_iff.1 hnE) (mem_fi24E_iff.1 fi24z_mem)
  have hgen : fi24EP ≤ C.map fi24Pi := by
    rw [fi24EP, MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ m24Sg := hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx'
    obtain ⟨n, -, hn⟩ := exists_fi24T_of_mem hx'
    refine ⟨n, ?_, hn⟩
    change (n : J) ∈ centralizer {fi24z}
    rw [mem_centralizer_singleton_iff]
    calc (n : J) * fi24z = (n : J) * fi24z * (n : J)⁻¹ * n := by group
      _ = fi24z * n := by rw [conj_fi24z hk hn]
  have hle : fi24EP.comap fi24Pi ≤ C :=
    calc fi24EP.comap fi24Pi ≤ (C.map fi24Pi).comap fi24Pi := comap_mono hgen
      _ = C ⊔ fi24Pi.ker := comap_map_eq _ _
      _ = C := sup_of_le_left hker
  obtain ⟨h, hP⟩ := mem_fi24T_iff.1 hs
  have hm : (⟨s, h⟩ : normalizer (fi24E : Set J)) ∈ C := hle (mem_comap.2 hP)
  have hc : (normalizer (fi24E : Set J)).subtype ⟨s, h⟩ ∈ centralizer {fi24z} := mem_comap.1 hm
  have e := mem_centralizer_singleton_iff.1 hc
  exact e

theorem fi24z_mem_omegaOneCenter : fi24z ∈ CFSG.Open.quasithinOmegaOneCenter fi24T := by
  unfold CFSG.Open.quasithinOmegaOneCenter
  exact subset_closure ⟨mem_inf.2 ⟨fi24E_le_fi24T fi24z_mem,
    mem_centralizer_iff.2 fun _ hs => comm_fi24z hs⟩, fi24E_sq _ fi24z_mem⟩

theorem eq_one_or_eq_fi24z {t : CFSG.Sporadic.Fi24.J} (hc : ∀ s ∈ fi24T, s * t = t * s) : t = 1 ∨ t = fi24z := by
  have htE : t ∈ fi24E := by
    rw [← centralizer_fi24E, mem_centralizer_iff]
    exact fun e he => hc e (fi24E_le_fi24T he)
  obtain ⟨S, hS⟩ := exists_bbarProd (mem_fi24E_iff.1 htE)
  obtain ⟨U, hU4, hUS⟩ := exists_card_le_four S
  rw [hS] at hUS
  have he : Even U.card := (bbarProd_mem_JR_iff U).1 (by rw [hUS]; exact jR_mem_JR t)
  have hcases : U.card = 0 ∨ U.card = 2 ∨ U.card = 4 := by
    obtain ⟨m, hm⟩ := he
    omega
  rcases hcases with h0 | h2 | h4
  · left
    rw [Finset.card_eq_zero.1 h0, bbarProd_empty] at hUS
    exact jR_injective (hUS.symm.trans (map_one jR).symm)
  · exact (@famProd_pair_false R inferInstance bbar bbar_comm bbar_sq fi24Sig fi24Sig_val
      (fun _ hS6 h1 => bbarProd_small hS6 h1) U h2 (bbarProd_fi24Sig hc hUS.symm)).elim
  · right
    obtain ⟨V, ⟨hV4, hV0⟩, hVU⟩ := exists_zero_mem h4
    have hVt : jR t = bP V := by rw [hVU, hUS]
    have hV := @famProd_tetrad_eq R inferInstance bbar bbar_comm bbar_sq fi24Sig fi24Sig_val
      (fun _ hS6 h1 => bbarProd_small hS6 h1) V hV4 hV0 (bbarProd_fi24Sig hc hVt)
    apply jR_injective
    rw [hVt, jR_fi24z, hV]
    rfl

end Cent

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
