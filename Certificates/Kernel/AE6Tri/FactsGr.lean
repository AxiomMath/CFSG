module

public import Certificates.Kernel.AE6Tri.FactsG
public import Certificates.Kernel.AE6Tri.Graph

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

@[expose] noncomputable def SG : Array (Array Nat) :=
  ((List.range 12).map fun j => unpack 720 10 (GD.S j)).toArray

@[expose] def baseGL : List (Fin 720) := [0, 2, 1, 4, 24, 8]

@[expose] def baseGA : Array Nat := (baseGL.map Fin.val).toArray

theorem SG_get {j : Nat} (hj : j < 12) : SG[j]! = unpack 720 10 (GD.S j) := by
  interval_cases j <;> rfl

theorem bindsG : Binds 720 10 GD.S 12 6 GD.BP SG baseGA := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SG], fun j hj => SG_get hj, rfl,
    fun t ht => ?_⟩
  interval_cases t <;> decide

theorem rawOKG : rawChainOK 720 (SG.extract 0 7) SG baseGA
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 7 12 gdDerive) 1 = true :=
  rawChainK_sound (NS := 15) (CH := 48) bindsG GD.head GD.hl (by norm_num) GD.hs

theorem extract_sizeG : (SG.extract 0 7).size = 7 := by simp [SG]

theorem extract_getG {i : Nat} (hi : i < 7) : (SG.extract 0 7)[i]! = SG[i]! :=
  CFSG.EvenSmallLie.OmegaEight.extract_getElem! hi (by simp [SG])

theorem permsG : allN 12 (fun j => permOK 720 10 (mask 10) (720 * 10) (GD.S j) (GD.SI j)) = true :=
  CertificateChecks.KernelAE6F.perm_head GD.head

theorem vl0_len : (vl.getD 0 []).length = 7 := by decide

@[expose] noncomputable def sP (j : Nat) : Equiv.Perm (Fin 720) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr (gP ((vl.getD 0 []).getD j 0)) (dP ((vl.getD 0 []).getD j 0)))

theorem genG : ∀ k < 7, permOfArr 720 SG[k]! = sP k := by
  refine fun k hk => grOK_sound gRep dRep (s := fun j => permOfArr 720 SG[j]!)
    (fun j hj => (Orb.prep_PS bindsG permsG (j := j) (by rw [vl0_len] at hj; omega)).1) kGensGD k
    (by rw [vl0_len]; exact hk)

theorem prodG : (rawOrbitSizes 720 SG baseGA).prod = 1290240 := by
  rw [rawOrbitSizesK_sound bindsG permsG GD.hl, ← Nat.eq_of_beq_eq_true kOrdGD]
  simp [List.range_succ]
  ring

theorem cardG : Nat.card (Subgroup.closure {g | ∃ k < 7, sP k = g}) = 1290240 := by
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 720) (O := SG.extract 0 7)
    (S := SG) (base := baseGL) (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 7 12 gdDerive)
    (chunks := 1) (by norm_num) (by decide) (by norm_num) (by rw [extract_sizeG]; simp [SG])
    (fun i hi => (extract_getG (extract_sizeG ▸ hi)).symm) (by rw [extract_sizeG]; exact rawOKG)
  have e : {g | ∃ k < (SG.extract 0 7).size, permOfArr 720 (SG.extract 0 7)[k]! = g} =
      {g | ∃ k < 7, sP k = g} := by
    ext g
    rw [extract_sizeG]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [extract_getG hk, genG k hk]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [extract_getG hk, genG k hk]⟩
  rw [e] at h
  rw [← prodG]
  exact h

@[expose] noncomputable def ddHom : AE6Om × AE6Om →* Equiv.Perm (Fin 720) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 360 ⊕ Fin 360 ≃ Fin 720)).toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin 360) (Fin 360)).comp (omegaT.subtype.prodMap omegaT.subtype))

theorem ddHom_apply (a b : AE6Om) :
    ddHom (a, b) = (finSumFinEquiv (m := 360) (n := 360)).permCongr
      (Equiv.sumCongr (a : Equiv.Perm (Fin 360)) (b : Equiv.Perm (Fin 360))) := rfl

theorem ddHom_injective : Function.Injective ddHom :=
  (Equiv.permCongrHom _).injective.comp
    (Equiv.Perm.sumCongrHom_injective.comp
      (omegaT.subtype_injective.prodMap omegaT.subtype_injective))

theorem dP_eq (i : Fin 8) : dP i.val = ((ae6Word (ae6Delta 0 i) : AE6Om) : Equiv.Perm (Fin 360)) := by
  rw [dP, delta_get.2.2 i, coe_ae6Word]

theorem vl0_of : ∀ k < 7, ∃ i : Fin 8, i ∈ ae6VertexLetters 0 ∧ (vl.getD 0 []).getD k 0 = i.val := by
  decide

theorem of_vl0 : ∀ i : Fin 8, i ∈ ae6VertexLetters 0 → ∃ k < 7, (vl.getD 0 []).getD k 0 = i.val := by
  decide

theorem map_graph : (Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters 0) =>
    (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta 0 i)))).map ddHom =
      Subgroup.closure {g | ∃ k < 7, sP k = g} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨k, hk, hki⟩ := of_vl0 i i.2
    refine ⟨k, hk, ?_⟩
    rw [ddHom_apply, sP, hki, ← dP_eq, ← coe_curtisGen]
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨i, hi, hki⟩ := vl0_of k hk
    refine ⟨_, ⟨⟨i, hi⟩, rfl⟩, ?_⟩
    rw [ddHom_apply, sP, hki, ← dP_eq, ← coe_curtisGen]

theorem card_graph : Nat.card (Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters 0) =>
    (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta 0 i)))) = 1290240 := by
  rw [← Subgroup.card_map_of_injective ddHom_injective, map_graph, cardG]

end CertificateChecks.KernelAE6Tri

end
