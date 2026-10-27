
module

public import CFSG.Quasithin.Vol2.KGFactC31M22RefBase

public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31E8
public import Certificates.Certificate7203

public section

namespace CFSG.Quasithin.KGC31.M22

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31 Matrix _root_.Certificates

theorem c_ord5 :
    ordTest 22 5 x5T = true := by
  obtain ⟨h, -⟩ := Certificates.certificate7203
  exact h

theorem c_ord7 :
    ordTest 22 7 x7T = true := by
  obtain ⟨-, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_ord11 :
    ordTest 22 11 x11T = true := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_orb5 :
    orbCheck 22 5 (orderTables m22Certificate 2) (powTabs 22 x5T 5) cands5 = true := by
  obtain ⟨-, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_orb7 :
    orbCheck 22 7 (orderTables m22Certificate 2) (powTabs 22 x7T 7) cands7 = true := by
  obtain ⟨-, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_act11 :
    actCheck 22 11 (orderTables m22Certificate 2) (powTabs 22 x11T 11) = true := by
  obtain ⟨-, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_invConj :
    invOK 22 hexConjT (invT 22 hexConjT) = true := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_eb_hex :
    ebasisOK 22 hexT = true := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_eb_duad :
    ebasisOK 22 duadT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_eb_e8 :
    ebasisOK 22 e8T = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_cent_hex_count :
    countProducts 22 (commAll 22 hexT) (levelTables m22Certificate) (idT 22) = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_norm_hex_count :
    countProducts 22 (normAll 22 hexT) (levelTables m22Certificate) (idT 22) = 5760 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_cent_duad_count :
    countProducts 22 (commAll 22 duadT) (levelTables m22Certificate) (idT 22) = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_norm_duad_count :
    countProducts 22 (normAll 22 duadT) (levelTables m22Certificate) (idT 22) = 1920 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_cent_e8_count :
    countProducts 22 (commAll 22 e8T) (levelTables m22Certificate) (idT 22) = 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_norm_e8_count :
    countProducts 22 (normAll 22 e8T) (levelTables m22Certificate) (idT 22) = 1344 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7203
  exact h

theorem c_hexChain_check :
    hexChain.check = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7203
  exact h

theorem c_hexChain_order :
    hexChain.orderCertificate = 5760 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7203
  exact h

theorem c_duadChain_check :
    duadChain.check = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7203
  exact h

theorem c_duadChain_order :
    duadChain.orderCertificate = 960 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7203
  exact h

theorem c_duad_in_chain :
    (duadT.all fun b => countProducts 22 (tblEq 22 b) (levelTables duadChain) (idT 22) == 1) =
      true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7203
  exact h

theorem c_masks_hex :
    (hexGen.zip hexMasks).all (fun p => masksOK 22 hexT (toTable p.1) p.2) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7203
  exact h

theorem c_masks_duad :
    (duadGen.zip duadMasks).all (fun p => masksOK 22 duadT (toTable p.1) p.2) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    Certificates.certificate7203
  exact h

theorem basis_hex : EBasis vHex :=
  EBasis.of_map (f := NativeSporadic.M22.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn22 forall₂_hex c_eb_hex)
theorem basis_duad : EBasis vDuad :=
  EBasis.of_map (f := NativeSporadic.M22.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn22 forall₂_duad c_eb_duad)
theorem basis_e8 : EBasis vE8 :=
  EBasis.of_map (f := NativeSporadic.M22.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn22 forall₂_e8 c_eb_e8)

theorem card_Mhex : Nat.card Mhex = 5760 := by
  rw [Mhex, card_genOf (Q := hexChain) (certificate_originalSubgroup _ _ _ _ _) c_hexChain_check,
    c_hexChain_order]

theorem card_Mduad : Nat.card Mduad = 960 := by
  rw [Mduad, card_genOf (Q := duadChain) (certificate_originalSubgroup _ _ _ _ _) c_duadChain_check,
    c_duadChain_order]

theorem conj_hex {j : ℕ} (hj : j < 2) (i : Fin 4) :
    elt (hexGenW.getD j []) * vHex i * (elt (hexGenW.getD j []))⁻¹ =
      eElt vHex fun r => matOf hexMasks j r i :=
  conj_gen forall₂_hex c_masks_hex (by rw [hexGenW_length]; exact hj)
    (by rw [hexMasks_length]; exact hj) i

theorem conj_duad {j : ℕ} (hj : j < 2) (i : Fin 4) :
    elt (duadGenW.getD j []) * vDuad i * (elt (duadGenW.getD j []))⁻¹ =
      eElt vDuad fun r => matOf duadMasks j r i :=
  conj_gen forall₂_duad c_masks_duad (by rw [duadGenW_length]; exact hj)
    (by rw [duadMasks_length]; exact hj) i

theorem hexGen_norm {j : ℕ} (hj : j < 2) :
    elt (hexGenW.getD j []) ∈ eNorm basis_hex :=
  mem_eNorm basis_hex (matOf hexMasks j) fun i => conj_hex hj i

theorem hexGen_eMat {j : ℕ} (hj : j < 2) :
    eMat basis_hex ⟨elt (hexGenW.getD j []), hexGen_norm hj⟩ = matOf hexMasks j :=
  eMat_eq basis_hex _ _ fun i => conj_hex hj i

theorem duadGen_norm {j : ℕ} (hj : j < 2) :
    elt (duadGenW.getD j []) ∈ eNorm basis_duad :=
  mem_eNorm basis_duad (matOf duadMasks j) fun i => conj_duad hj i

theorem duadGen_eMat {j : ℕ} (hj : j < 2) :
    eMat basis_duad ⟨elt (duadGenW.getD j []), duadGen_norm hj⟩ = matOf duadMasks j :=
  eMat_eq basis_duad _ _ fun i => conj_duad hj i

theorem Mhex_le_ovStab : Mhex ≤ Hex.ovStab basis_hex :=
  genOf_le hexGenW_length fun j hj => ⟨hexGen_norm hj, fun i => by
    rw [Hex.ovImg, hexGen_eMat hj]
    exact hexMat_perm j hj i⟩

theorem Mhex_le_eNorm : Mhex ≤ eNorm basis_hex :=
  fun _ hx => (Mhex_le_ovStab hx).1

theorem card_eNorm_hex : Nat.card (eNorm basis_hex) = 5760 :=
  card_normalizer_eq basis_hex forall₂_hex c_norm_hex_count

theorem Mhex_eq : Mhex = eNorm basis_hex :=
  Subgroup.eq_of_le_of_card_ge Mhex_le_eNorm (by rw [card_eNorm_hex, card_Mhex])

theorem cent_hex :
    Subgroup.centralizer (eSub basis_hex : Set G₀) ≤ eSub basis_hex :=
  centralizer_le_of_card basis_hex (card_centralizer_eq basis_hex forall₂_hex c_cent_hex_count)

theorem refData_hex : RefData (eSub basis_hex) Mhex where
  cent := cent_hex
  comm := fun a ha b hb => eSub_comm basis_hex a b ha hb
  le := Mhex_eq ▸ Subgroup.le_normalizer
  norm := Mhex_le_eNorm
  perf := perf_of_card Mhex_le_eNorm (by rw [card_eNorm_hex, card_Mhex]; norm_num)
  simple := by
    have hVL : eSub basis_hex ≤ Mhex := Mhex_eq ▸ Subgroup.le_normalizer
    obtain ⟨α, hα, hker, -⟩ := Hex.exists_ovAlt basis_hex Mhex_le_ovStab hVL
      (inf_le_right.trans cent_hex) (by rw [card_Mhex])
    have := Hex.alt6_simple
    exact simple_of_surj α hα hker

theorem Mduad_le_f4Stab : Mduad ≤ Duad.f4Stab basis_duad :=
  genOf_le duadGenW_length fun j hj => ⟨duadGen_norm hj, by
    rw [duadGen_eMat hj]
    exact duadMat_comm j hj⟩

theorem Mduad_le_eNorm : Mduad ≤ eNorm basis_duad :=
  fun _ hx => (Mduad_le_f4Stab hx).1

theorem duadGen_f4 {j : ℕ} (hj : j < 2) :
    elt (duadGenW.getD j []) ∈ Duad.f4Stab basis_duad :=
  ⟨duadGen_norm hj, by rw [duadGen_eMat hj]; exact duadMat_comm j hj⟩

theorem Mduad_det (x : ↥Mduad) :
    (Duad.f4Mat (eMat basis_duad ⟨x, (Mduad_le_f4Stab x.2).1⟩)).det = 1 := by
  let D : ↥(Duad.f4Stab basis_duad) →* (Duad.F4)ˣ :=
    Matrix.GeneralLinearGroup.det.comp (Duad.f4Rep basis_duad)
  let K : Subgroup G₀ := D.ker.map (Duad.f4Stab basis_duad).subtype
  have hmemK : ∀ (y : G₀) (hy : y ∈ Duad.f4Stab basis_duad),
      (Duad.f4Mat (eMat basis_duad ⟨y, hy.1⟩)).det = 1 → y ∈ K := by
    intro y hy hd
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    show D ⟨y, hy⟩ = 1
    apply Units.ext
    simpa [D, Duad.f4Rep_coe] using hd
  have hle : Mduad ≤ K := genOf_le duadGenW_length fun j hj =>
    hmemK _ (duadGen_f4 hj) (by rw [duadGen_eMat hj]; exact duadMat_det j hj)
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have h2 : (Duad.f4Mat (eMat basis_duad ⟨y, y.2.1⟩)).det = 1 := by
    have h3 := congrArg Units.val (show D y = 1 from hy)
    simpa [D, Duad.f4Rep_coe] using h3
  have hyx' : (⟨(y : G₀), y.2.1⟩ : ↥(eNorm basis_duad)) = ⟨x, (Mduad_le_f4Stab x.2).1⟩ :=
    Subtype.ext hyx
  rwa [hyx'] at h2

theorem cent_duad :
    Subgroup.centralizer (eSub basis_duad : Set G₀) ≤ eSub basis_duad :=
  centralizer_le_of_card basis_duad
    (card_centralizer_eq basis_duad forall₂_duad c_cent_duad_count)

theorem card_eNorm_duad :
    Nat.card (eNorm basis_duad) = 1920 :=
  card_normalizer_eq basis_duad forall₂_duad c_norm_duad_count

theorem vDuad_mem (i : Fin 4) : vDuad i ∈ Mduad := by
  classical
  have h := c_duad_in_chain
  rw [List.all_eq_true] at h
  obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem forall₂_duad (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have h1 := h b hb
  rw [beq_iff_eq] at h1
  have hQ : ValidSchreier duadChain := c_duadChain_check
  have hc := card_subtype_eq_countProducts hn22 duadChain hQ
    (P := fun g => ((vDuad i : G₀) : Equiv.Perm (Fin 22)) = g)
    (fun T g hT => tblEq_iff_eq hbi hT)
  rw [h1] at hc
  have hne : Nonempty {x : duadChain.originalSubgroup //
      ((vDuad i : G₀) : Equiv.Perm (Fin 22)) = x} := by
    have hpos : 0 < Nat.card {x : duadChain.originalSubgroup //
        ((vDuad i : G₀) : Equiv.Perm (Fin 22)) = x} := by rw [hc]; norm_num
    exact (Nat.card_pos_iff.mp hpos).1
  obtain ⟨⟨x, hx⟩⟩ := hne
  have hmem : ((vDuad i : G₀) : Equiv.Perm (Fin 22)) ∈ duadChain.originalSubgroup := hx ▸ x.2
  rw [duadChain, certificate_originalSubgroup, duadGen, ← map_genOf] at hmem
  obtain ⟨y, hy, hyv⟩ := hmem
  rw [Subtype.val_injective hyv] at hy
  exact hy

theorem refData_duad : RefData (eSub basis_duad) Mduad where
  cent := cent_duad
  comm := fun a ha b hb => eSub_comm basis_duad a b ha hb
  le := by
    rw [eSub_eq_closure, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact vDuad_mem i
  norm := Mduad_le_eNorm
  perf := perf_of_card Mduad_le_eNorm (by rw [card_eNorm_duad, card_Mduad])
  simple := by
    have hVL : eSub basis_duad ≤ Mduad := by
      rw [eSub_eq_closure, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact vDuad_mem i
    let φ := Duad.f4Hom basis_duad Mduad_le_f4Stab Mduad_det
    have hker : φ.ker = (eSub basis_duad).subgroupOf Mduad := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        have h2 : Duad.f4Rep basis_duad (Subgroup.inclusion Mduad_le_f4Stab x) = 1 :=
          congrArg Subtype.val h1
        exact cent_duad ((Duad.f4Rep_eq_one_iff basis_duad _).mp h2)
      · intro hx
        apply Subtype.ext
        refine (Duad.f4Rep_eq_one_iff basis_duad (Subgroup.inclusion Mduad_le_f4Stab x)).mpr ?_
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_duad _ _ hy hx
    have hsurj : Function.Surjective φ := by
      have h1 := card_range_eq hVL φ hker
      rw [card_eSub, card_Mduad] at h1
      have h2 : Nat.card φ.range = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 Duad.F4) := by
        rw [Duad.card_statedSL]; omega
      rw [← MonoidHom.range_eq_top]
      exact Subgroup.eq_top_of_card_eq _ h2
    have := Duad.isSimpleGroup_statedSL
    exact simple_of_surj φ hsurj hker

theorem cent_e8 :
    Subgroup.centralizer (eSub basis_e8 : Set G₀) ≤ eSub basis_e8 :=
  centralizer_le_of_card basis_e8 (card_centralizer_eq basis_e8 forall₂_e8 c_cent_e8_count)

theorem card_eNorm_e8 : Nat.card (eNorm basis_e8) = 1344 :=
  card_normalizer_eq basis_e8 forall₂_e8 c_norm_e8_count

theorem refData_e8 :
    RefData (eSub basis_e8) (eNorm basis_e8) where
  cent := cent_e8
  comm := fun a ha b hb => eSub_comm basis_e8 a b ha hb
  le := Subgroup.le_normalizer
  norm := le_rfl
  perf := fun _ hK _ => hK
  simple := by
    let φ := E8.e3Hom basis_e8 (X := eNorm basis_e8) le_rfl
    have hker : φ.ker = (eSub basis_e8).subgroupOf (eNorm basis_e8) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
      constructor
      · intro h; exact cent_e8 h
      · intro hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_e8 _ _ hy hx
    have hsurj : Function.Surjective φ := by
      have h1 := card_range_eq Subgroup.le_normalizer φ hker
      rw [card_eSub, card_eNorm_e8] at h1
      have h2 : Nat.card φ.range = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
        rw [E8.card_statedSL3]; omega
      rw [← MonoidHom.range_eq_top]
      exact Subgroup.eq_top_of_card_eq _ h2
    have := E8.isSimpleGroup_statedSL3
    exact simple_of_surj φ hsurj hker

theorem orderOf_x5 : orderOf x5 = 5 := orderOf_elt (by norm_num) c_ord5
theorem orderOf_x7 : orderOf x7 = 7 := orderOf_elt (by norm_num) c_ord7
theorem orderOf_x11 : orderOf x11 = 11 := orderOf_elt (by norm_num) c_ord11

theorem orbSub_cases5 {y t : G₀}
    (hy : y ∈ Subgroup.zpowers x5) (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < 5, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    orbSub y t = eSub basis_duad ∨ orbSub y t = eSub basis_hex ∨
      orbSub y t = (eSub basis_hex).map (MulAut.conj cHex).toMonoidHom := by
  obtain ⟨e, he, hey⟩ := exists_powTab rfl orderOf_x5 hy
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  have hy5 : (y : Equiv.Perm (Fin 22)) ^ 5 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← Subgroup.coe_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, ← orderOf_x5, pow_orderOf_eq_one, _root_.one_zpow, Subgroup.coe_one]
  have hc : Rep 22 hexConjT ((cHex : G₀) : Equiv.Perm (Fin 22)) := rep_elt hexConjW
  have hci : Rep 22 (invT 22 hexConjT) ((cHex : G₀) : Equiv.Perm (Fin 22))⁻¹ :=
    Rep.inv_of_invOK hc c_invConj
  have hcands : List.Forall₂ (List.Forall₂ (Rep 22)) cands5
      [List.ofFn fun i => ((vDuad i : G₀) : Equiv.Perm (Fin 22)),
        List.ofFn fun i => ((vHex i : G₀) : Equiv.Perm (Fin 22)),
        List.ofFn fun i => ((cHex : G₀) : Equiv.Perm (Fin 22)) * ((vHex i : G₀) :
          Equiv.Perm (Fin 22)) * ((cHex : G₀) : Equiv.Perm (Fin 22))⁻¹] := by
    refine .cons forall₂_duad (.cons forall₂_hex (.cons ?_ .nil))
    have h2 : (List.ofFn fun i => ((cHex : G₀) : Equiv.Perm (Fin 22)) * ((vHex i : G₀) :
        Equiv.Perm (Fin 22)) * ((cHex : G₀) : Equiv.Perm (Fin 22))⁻¹) =
        (List.ofFn fun i => ((vHex i : G₀) : Equiv.Perm (Fin 22))).map
          fun g => ((cHex : G₀) : Equiv.Perm (Fin 22)) * g * ((cHex : G₀) :
            Equiv.Perm (Fin 22))⁻¹ := by
      rw [List.map_ofFn]; rfl
    rw [h2, hex2T]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact forall₂_hex.imp fun b g hb => Rep.compT (Rep.compT hc hb) hci
  obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn22 c_orb5 hcands he hT hey hTt (by norm_num)
    hy5 hmove' hcomm'
  have hmap : (orbSub y t).map NativeSporadic.M22.subtype =
      orbSub (y : Equiv.Perm (Fin 22)) (t : Equiv.Perm (Fin 22)) := orbSub_map _ y t
  have hinj := Subgroup.map_injective (f := NativeSporadic.M22.subtype) Subtype.val_injective
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcg
  rcases hcg with rfl | rfl | rfl
  · left; exact hinj (by rw [hmap, hcl, closure_ofFn basis_duad])
  · right; left; exact hinj (by rw [hmap, hcl, closure_ofFn basis_hex])
  · right; right; exact hinj (by rw [hmap, hcl, closure_ofFn_conj basis_hex])

theorem orbSub_cases7 {y t : G₀}
    (hy : y ∈ Subgroup.zpowers x7) (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < 7, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    orbSub y t = eSub basis_e8 := by
  obtain ⟨e, he, hey⟩ := exists_powTab rfl orderOf_x7 hy
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  have hy7 : (y : Equiv.Perm (Fin 22)) ^ 7 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← Subgroup.coe_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, ← orderOf_x7, pow_orderOf_eq_one, _root_.one_zpow, Subgroup.coe_one]
  have hcands : List.Forall₂ (List.Forall₂ (Rep 22)) cands7
      [List.ofFn fun i => ((vE8 i : G₀) : Equiv.Perm (Fin 22))] :=
    .cons forall₂_e8 .nil
  obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn22 c_orb7 hcands he hT hey hTt (by norm_num)
    hy7 hmove' hcomm'
  have hmap : (orbSub y t).map NativeSporadic.M22.subtype =
      orbSub (y : Equiv.Perm (Fin 22)) (t : Equiv.Perm (Fin 22)) := orbSub_map _ y t
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcg
  subst hcg
  exact Subgroup.map_injective (f := NativeSporadic.M22.subtype) Subtype.val_injective
    (by rw [hmap, hcl, closure_ofFn basis_e8])

theorem not_bad11 {y t : G₀}
    (hy : y ∈ Subgroup.zpowers x11) (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < 11, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) : False := by
  obtain ⟨e, he, hey⟩ := exists_powTab rfl orderOf_x11 hy
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  exact false_of_actCheck hn22 c_act11 hT he hey hTt hmove' hcomm'

end CFSG.Quasithin.KGC31.M22

end
