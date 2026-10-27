module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import Certificates.Certificate4202

public section

namespace CFSG.Quasithin.J4M2

open CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

theorem chkSig_true : chkSig = true :=
  Certificates.certificate4202.1

theorem chkHex_true : chkHex = true :=
  Certificates.certificate4202.2.1

theorem chkWords_true : chkWords = true :=
  Certificates.certificate4202.2.2.1

theorem chkT_true : chkT = true :=
  Certificates.certificate4202.2.2.2.1

theorem chkClass_true : chkClass = true :=
  Certificates.certificate4202.2.2.2.2

theorem hexB_injective : Function.Injective hexB := by
  intro i j hij
  have h := chkHex_true
  unfold chkHex at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, h3⟩, -⟩ := h
  have h5 := List.all_eq_true.1 (List.all_eq_true.1 h3 i (List.mem_finRange i)) j
    (List.mem_finRange j)
  rw [Bool.or_eq_true] at h5
  rcases h5 with h5 | h5
  · exact beq_iff_eq.1 h5
  · rw [hij] at h5
    simp at h5

theorem permutesHex_of_mem {g : Equiv.Perm (Fin 22)}
    (hg : g ∈ blockGens) : ∀ i, ∃ j, (hexB i).image g = hexB j := by
  have h := chkHex_true
  unfold chkHex at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h4⟩ := h
  have h5 := List.all_eq_true.1 h4 g hg
  intro i
  obtain ⟨j, -, hj⟩ := List.any_eq_true.1 (List.all_eq_true.1 h5 i (List.mem_finRange i))
  exact ⟨j, beq_iff_eq.1 hj⟩

theorem mem_blockGens_of_mem_mGens {g : Equiv.Perm (Fin 22)} (hg : g ∈ mGens) :
    g ∈ blockGens :=
  List.mem_append_left _ (List.mem_append_left _ hg)

theorem M22_le_blockStab :
    NativeSporadic.M22 ≤ blockStab hexB hexB_injective := by
  rw [← mGens_closure]
  exact closure_le_blockStab hexB hexB_injective _ fun g hg =>
    permutesHex_of_mem (mem_blockGens_of_mem_mGens hg)

@[expose] noncomputable def Phi :
    ↥NativeSporadic.M22 →* Equiv.Perm (Fin 77) :=
  restrictedBlockHom hexB hexB_injective M22_le_blockStab

theorem Phi_spec (g : ↥NativeSporadic.M22) (i : Fin 77) :
    (hexB i).image (g : Equiv.Perm (Fin 22)) = hexB (Phi g i) :=
  restrictedBlockHom_spec M22_le_blockStab g i

theorem find?_hexB (j : Fin 77) :
    (List.finRange 77).find? (fun k => hexB k == hexB j) = some j := by
  have hs : ((List.finRange 77).find? (fun k => hexB k == hexB j)).isSome = true :=
    List.find?_isSome.2 ⟨j, List.mem_finRange j, beq_self_eq_true _⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hs
  have hk' := List.find?_some hk
  rw [hk]
  congr 1
  exact hexB_injective (beq_iff_eq.1 hk')

theorem phiRN_get (g : Equiv.Perm (Fin 22)) (i j : Fin 77)
    (h : (hexB i).image g = hexB j) : (phiRN g).val[i] = j := by
  simp only [phiRN, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  rw [h, find?_hexB]
  rfl

theorem RN_enc_Phi (g : ↥NativeSporadic.M22) :
    RN.enc (Phi g) = phiRN (g : Equiv.Perm (Fin 22)) := by
  refine RN.ext fun i => ?_
  rw [RN.enc_get]
  exact (phiRN_get _ i _ (Phi_spec g i)).symm

theorem phiRN_eq_one_of_fix (g : Equiv.Perm (Fin 22))
    (h : ∀ i, (hexB i).image g = hexB i) : phiRN g = 1 := by
  refine RN.ext fun i => ?_
  rw [phiRN_get g i i (h i), RN.one_get]

theorem phiRN_mGens_zero_ne_one :
    phiRN (mGens.getD 0 1) ≠ 1 := by
  have h := chkWords_true
  unfold chkWords at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  exact bne_iff_ne.1 h1

theorem mGens_getD_mem (k : ℕ) (hk : k < 2) : mGens.getD k 1 ∈ NativeSporadic.M22 := by
  rw [← mGens_closure]
  apply Subgroup.subset_closure
  show mGens.getD k 1 ∈ mGens
  rw [List.getD_eq_getElem _ _ (by simpa [mGens] using hk)]
  exact List.getElem_mem _

theorem Phi_injective :
    Function.Injective (Phi : ↥NativeSporadic.M22 →* Equiv.Perm (Fin 77)) := by
  have : IsSimpleGroup ↥NativeSporadic.M22 := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  refine restrictedBlockHom_injective_of_simple M22_le_blockStab ?_
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  exact phiRN_mGens_zero_ne_one (phiRN_eq_one_of_fix _ fun i =>
    hcon _ (mGens_getD_mem 0 (by norm_num)) i)

theorem M22_le_of_mGens {X : Subgroup (Equiv.Perm (Fin 22))} (h : ∀ g ∈ mGens, g ∈ X) :
    NativeSporadic.M22 ≤ X := by
  rw [← mGens_closure]
  exact (Subgroup.closure_le X).2 h

@[expose] def genA22 : ↥NativeSporadic.M22 := ⟨mGens.getD 0 1, mGens_getD_mem 0 (by norm_num)⟩

@[expose] def genB22 : ↥NativeSporadic.M22 := ⟨mGens.getD 1 1, mGens_getD_mem 1 (by norm_num)⟩

@[expose] def MbarP : Subgroup (Equiv.Perm (Fin 77)) := Subgroup.closure {x | x ∈ oddPerms}

theorem phiRN_genA22_eq :
    phiRN (mGens.getD 0 1) = evalW (oddPerms.map RN.enc) wordPhiA := by
  have h := chkWords_true
  unfold chkWords at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, h2⟩, -⟩, -⟩ := h
  exact beq_iff_eq.1 h2

theorem phiRN_genB22_eq :
    phiRN (mGens.getD 1 1) = evalW (oddPerms.map RN.enc) wordPhiB := by
  have h := chkWords_true
  unfold chkWords at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, h3⟩, -⟩ := h
  exact beq_iff_eq.1 h3

theorem enc_oddPerms_eq {k : ℕ} (hk : k < 5) :
    RN.enc (oddPerms.getD k 1) =
      evalW [phiRN (mGens.getD 0 1), phiRN (mGens.getD 1 1)] (wordsOdd.getD k []) := by
  have h := chkWords_true
  unfold chkWords at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h4⟩ := h
  exact beq_iff_eq.1 (List.all_eq_true.1 h4 k (List.mem_range.2 hk))

theorem Phi_genA22 : Phi genA22 = evalW oddPerms wordPhiA := by
  apply RN.enc_inj
  rw [RN_enc_Phi, enc_evalW (rawIsEnc 77)]
  exact phiRN_genA22_eq

theorem Phi_genB22 : Phi genB22 = evalW oddPerms wordPhiB := by
  apply RN.enc_inj
  rw [RN_enc_Phi, enc_evalW (rawIsEnc 77)]
  exact phiRN_genB22_eq

theorem Phi_mem_of_gens {S : Subgroup (Equiv.Perm (Fin 77))}
    (hA : Phi genA22 ∈ S) (hB : Phi genB22 ∈ S) (g : ↥NativeSporadic.M22) : Phi g ∈ S := by
  have h : NativeSporadic.M22 ≤ (S.comap Phi).map NativeSporadic.M22.subtype := by
    refine M22_le_of_mGens fun x hx => ?_
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨genA22, hA, rfl⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨genB22, hB, rfl⟩
      · exact absurd hx List.not_mem_nil
  obtain ⟨k, hk, hkg⟩ := h g.2
  have hkg' : k = g := Subtype.ext hkg
  rw [← hkg']
  exact hk

theorem range_Phi :
    (Phi : ↥NativeSporadic.M22 →* Equiv.Perm (Fin 77)).range = MbarP := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    refine Phi_mem_of_gens ?_ ?_ g
    · rw [Phi_genA22]
      exact evalW_mem_closure oddPerms _
    · rw [Phi_genB22]
      exact evalW_mem_closure oddPerms _
  · rw [MbarP, Subgroup.closure_le]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have hk5 : k < 5 := by simpa [oddPerms] using hk
    rw [SetLike.mem_coe]
    have hx5 : oddPerms[k]'hk = oddPerms.getD k 1 := (List.getD_eq_getElem _ _ hk).symm
    rw [hx5]
    have henc := enc_oddPerms_eq (k := k) hk5
    have e1 : phiRN (mGens.getD 0 1) = RN.enc (Phi genA22) := (RN_enc_Phi genA22).symm
    have e2 : phiRN (mGens.getD 1 1) = RN.enc (Phi genB22) := (RN_enc_Phi genB22).symm
    rw [e1, e2] at henc
    have henc' : RN.enc (oddPerms.getD k 1) =
        RN.enc (evalW [Phi genA22, Phi genB22] (wordsOdd.getD k [])) := by
      rw [enc_evalW (rawIsEnc 77)]
      exact henc
    rw [RN.enc_inj henc']
    refine (Subgroup.closure_le _).2 ?_ (evalW_mem_closure [Phi genA22, Phi genB22] _)
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨genA22, rfl⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨genB22, rfl⟩
      · exact absurd hy List.not_mem_nil

@[expose] noncomputable def phiEquiv :
    ↥NativeSporadic.M22 ≃* ↥MbarP :=
  (MonoidHom.ofInjective Phi_injective).trans (MulEquiv.subgroupCongr range_Phi)

theorem card_MbarP :
    Nat.card ↥MbarP = 443520 := by
  rw [← Nat.card_congr phiEquiv.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M22

theorem isSimpleGroup_MbarP :
    IsSimpleGroup ↥MbarP := by
  have : IsSimpleGroup ↥NativeSporadic.M22 := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  exact MulEquiv.isSimpleGroup phiEquiv.symm

theorem MbarP_nonabelian :
    ∃ a b : ↥MbarP, a * b ≠ b * a := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have := isSimpleGroup_MbarP
  let _ : CommGroup ↥MbarP := { (inferInstance : Group ↥MbarP) with mul_comm := hcon }
  have hp := IsSimpleGroup.prime_card (α := ↥MbarP)
  rw [card_MbarP] at hp
  norm_num at hp

end CFSG.Quasithin.J4M2
