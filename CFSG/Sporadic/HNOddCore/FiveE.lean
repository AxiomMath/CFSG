module

public import CFSG.Sporadic.HNOddCore.FiveD
public import Certificates.Certificate2085
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv Equiv.Perm

theorem range_pt_univ {M : ℕ} {L : Array ℕ} (hL : PtList M L) (h : L.size = M) :
    Set.range hL.pt = Set.univ := by
  have hb : Function.Bijective hL.pt :=
    (Fintype.bijective_iff_injective_and_card hL.pt).2 ⟨hL.pt_injective, by simp [h]⟩
  exact Set.range_eq_univ.2 hb.2

theorem card_sup_of_comm {G0 : Type*} [Group G0] {J : Subgroup G0} [Finite J] {A B : Subgroup J}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup J) = Nat.card A * Nat.card B := by
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype
      fun a b => show Commute (A.subtype a) (B.subtype b) from hc a a.2 b b.2).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype
      fun a b => show Commute (A.subtype a) (B.subtype b) from hc a a.2 b b.2) := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have h' : (a1 : J) * b1 = a2 * b2 := h
    have hab : (a2 : J)⁻¹ * a1 = b2 * (b1 : J)⁻¹ := by
      calc (a2 : J)⁻¹ * a1 = (a2 : J)⁻¹ * (a1 * b1) * (b1 : J)⁻¹ := by group
        _ = (a2 : J)⁻¹ * (a2 * b2) * (b1 : J)⁻¹ := by rw [h']
        _ = b2 * (b1 : J)⁻¹ := by group
    have hmem : (a2 : J)⁻¹ * a1 ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a2.2) a1.2, hab ▸ B.mul_mem b2.2 (B.inv_mem b1.2)⟩
    rw [hi, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hb : (b2 : J) * (b1 : J)⁻¹ = 1 := by rw [← hab, hmem, inv_mul_cancel]
    rw [mul_inv_eq_one] at hb
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb.symm)
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod]

theorem mem_sup_of_comm {G0 : Type*} [Group G0] {J : Subgroup G0} {A B : Subgroup J}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : J} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype
      fun a b => show Commute (A.subtype a) (B.subtype b) from hc a a.2 b b.2).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem x0_eq_pt0 :
    omList.pt ⟨0, by rw [fFixed_size]; norm_num⟩ = x0 := Fin.ext rfl

theorem omPt_injective :
    Function.Injective omPt := fun a b h =>
  Fin.ext (by have := omList.pt_injective h; simpa using congrArg Fin.val this)

theorem range_omList :
    Set.range omList.pt = Set.range omPt := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, by rw [← fFixed_size]; exact k.2⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, rfl⟩

theorem closure_iSm_eq :

    Subgroup.closure (Set.range fun s : Fin iSm.size => iGen s) = IJ := by
  have hsz : iSm.size = 6 := by simp [iSm, iSmall_size]
  rw [IJ_eq]
  congr 1
  refine Set.ext fun _ => ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, by have := s.2; omega⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, by have := s.2; omega⟩, rfl⟩

theorem iOrbit_parts :
    orbitCertOK FAData.fFixed.toArray.size iSm orbI (posArr 50 orbI)
    (orbitRecs iSm orbI (posArr 50 orbI)).1 (orbitRecs iSm orbI (posArr 50 orbI)).2 = true ∧
    orbI.size = 50 := by
  have h := five_small_parts.2.2.1
  unfold iOrbitOK orbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [fFixed_size]
  exact ⟨h.1.2, h.2⟩

theorem orbit_IJ :
    MulAction.orbit IJ x0 = Set.range omPt := by
  obtain ⟨hc, hsz⟩ := iOrbit_parts
  have h := orbit_eq_of_cert omList hactI hc
  dsimp only at h
  rw [closure_iSm_eq, range_pt_univ _ (by rw [hsz, fFixed_size]), Set.image_univ] at h
  have hx0 : x0 ∈ MulAction.orbit IJ (omList.pt ((ptList_of_pointsOK
      (orbitCertOK_spec hc).2.1).pt ⟨0, (orbitCertOK_spec hc).1⟩)) := by
    rw [h, ← x0_eq_pt0]
    exact ⟨_, rfl⟩
  rw [MulAction.orbit_eq_iff.2 hx0, h, range_omList]

theorem card_orbit_IJ :
    (MulAction.orbit IJ x0).ncard = 50 := by
  rw [orbit_IJ, Set.ncard_range_of_injective omPt_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem AJ_le_IJ :
    AJ ≤ IJ := fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem stab_IJ
    {g : JH} (hg : g ∈ IJ) : g • x0 = x0 ↔ g ∈ AJ := by
  constructor
  · intro h
    rw [AJ_eq]
    exact five_stab (by rw [← IJ_eq]; exact hg) h
  · intro h
    exact (mem_HJ_iff_fix _).1 (AJ_le_HJ h)

theorem card_IJ :
    Nat.card IJ = 126000 := by
  have hidx := MulAction.index_stabilizer IJ x0
  rw [card_orbit_IJ] at hidx
  have heq : MulAction.stabilizer IJ x0 = AJ.subgroupOf IJ := by
    ext ⟨g, hg⟩
    rw [Subgroup.mem_subgroupOf]
    exact stab_IJ hg
  have hmul := (MulAction.stabilizer IJ x0).card_mul_index
  rw [hidx, heq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe AJ_le_IJ).toEquiv, card_AJ] at hmul
  rw [← hmul]

theorem IJ_le_CJ :
    IJ ≤ Subgroup.centralizer {fJ} := by
  rw [IJ_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact (Subgroup.mem_centralizer_singleton_iff (g := fJ) (k := iGen k)).2 (fJ_comm_iGen k).symm

theorem mem_omega_of_comm
    {c : JH} (hc : c ∈ Subgroup.centralizer {fJ}) {x : X}
    (hx : x ∈ Set.range omPt) : c • x ∈ Set.range omPt := by
  have hcf : c * fJ = fJ * c := (Subgroup.mem_centralizer_singleton_iff (g := fJ) (k := c)).1 hc
  obtain ⟨k, rfl⟩ := hx
  have hk : fJ • omPt k = omPt k := (fix_fJ _).2 ⟨k, rfl⟩
  exact (fix_fJ _).1 (by rw [← mul_smul, ← hcf, mul_smul, hk])

theorem sub_isSimpleGroup_of_bijective' {G G' : Type*} [Group G] [Group G'] {H : Subgroup G}
    {K : Subgroup G'} (f : H →* K) (hf : Function.Bijective f) (hH : IsSimpleGroup H) :
    IsSimpleGroup K :=
  (MulEquiv.ofBijective f hf).isSimpleGroup_congr.1 hH

@[expose] def ahToAJ :
    AH →* AJ :=
  (HJ.subtype.comp AH.subtype).codRestrict AJ fun h => ⟨h, h.2, rfl⟩

theorem ahToAJ_bijective :
    Function.Bijective ahToAJ := by
  constructor
  · intro a b h
    have e := Subtype.ext_iff.1 h
    exact Subtype.ext (Subtype.ext e)
  · rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem AJ_simple :
    IsSimpleGroup AJ :=
  sub_isSimpleGroup_of_bijective' ahToAJ ahToAJ_bijective AH_simple

theorem iSm01 : (iSm[0]!)[1]! = 47 := by
  rw [iSm_get (by norm_num)]
  rfl

theorem aGen0_omPt1 :
    aGenJ 0 • omPt 1 = omPt 47 := by
  obtain ⟨h, he⟩ := hactI 0 (by simp [iSm, iSmall_size])
    ⟨1, by rw [fFixed_size]; norm_num⟩
  have e1 : iGen 0 = aGenJ 0 := ite_eq_left (by norm_num)
  rw [e1] at he
  exact he.trans (congrArg omList.pt (Fin.ext iSm01))

theorem IJ_faithful
    {g : JH} (hg : g ∈ IJ) (hfix : ∀ k, g • omPt k = omPt k) : g = 1 := by
  have hgA : g ∈ AJ := (stab_IJ hg).1 (by
    have := hfix ⟨0, by norm_num⟩
    rwa [show omPt ⟨0, by norm_num⟩ = x0 from x0_eq_pt0] at this)
  let K : Subgroup AJ :=
    { carrier := {a | ∀ k, (a : JH) • omPt k = omPt k}
      mul_mem' := fun {a b} ha hb k => by
        show ((a : JH) * b) • omPt k = omPt k
        rw [mul_smul, hb k, ha k]
      one_mem' := fun k => one_smul _ _
      inv_mem' := fun {a} ha k => by
        show (a : JH)⁻¹ • omPt k = omPt k
        rw [inv_smul_eq_iff, ha k] }
  have hKn : K.Normal := ⟨fun a ha b k => by
    have hbC : ((b : JH))⁻¹ ∈ Subgroup.centralizer {fJ} :=
      IJ_le_CJ (AJ_le_IJ (AJ.inv_mem b.2))
    obtain ⟨j, hj⟩ := mem_omega_of_comm hbC ⟨k, rfl⟩
    show ((b : JH) * a * (b : JH)⁻¹) • omPt k = omPt k
    rw [mul_smul, mul_smul, ← hj, ha j, hj, smul_inv_smul]⟩
  rcases AJ_simple.eq_bot_or_eq_top_of_normal K with h | h
  · have hmem : (⟨g, hgA⟩ : AJ) ∈ K := hfix
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have ha : aGenJ 0 ∈ AJ := by
      rw [AJ_eq]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    have hmem : (⟨aGenJ 0, ha⟩ : AJ) ∈ K := h ▸ Subgroup.mem_top _
    have := hmem 1
    rw [show ((⟨aGenJ 0, ha⟩ : AJ) : JH) = aGenJ 0 from rfl, aGen0_omPt1] at this
    exact absurd (omPt_injective this) (by decide)

end CFSG.Sporadic.HNOddCore
