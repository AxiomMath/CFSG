module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseB
public import CFSG.Quasithin.Recognition.Stroth.Str83TorusInj
public import CFSG.Quasithin.Vol2.Ch11SecC37N1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_hallTwoPrime_borelOf {L S D : Subgroup G}
    (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hD : RonanF13.HallTwoPrime D (borelOf L S))
    {x : G} (hx : x ∈ borelOf L S) (hodd : Odd (orderOf x)) :
    ∃ u ∈ S ⊓ L, u * x * u⁻¹ ∈ D := by
  classical
  have hsyl' : IsSylowTwoOf (S ⊓ L) (borelOf L S) :=
    F7.isSylowTwoOf_mono_right hsyl (F1.sylow_le_borelOf L S) (F1.borelOf_le L S)
  have hnorm : borelOf L S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    F1.borelOf_le_normalizer L S
  have hhall : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf D (borelOf L S) := hD
  have hE : Subgroup.zpowers x ≤ borelOf L S := Subgroup.zpowers_le.mpr hx
  have hoddE : Odd (Nat.card ↥(Subgroup.zpowers x)) := by
    rwa [Nat.card_zpowers]
  obtain ⟨p, hp, hle⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecC.exists_conj_le_of_normal_sylow hsyl' hnorm hhall hE hoddE
  refine ⟨p⁻¹, (S ⊓ L).inv_mem hp, ?_⟩
  have hxmap : x ∈ D.map (MulAut.conj p).toMonoidHom := hle (Subgroup.mem_zpowers x)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
  have hyx' : (MulAut.conj p) y = x := hyx
  have hgoal : p⁻¹ * x * (p⁻¹)⁻¹ = y := by
    rw [← hyx', MulAut.conj_apply]
    group
  rwa [hgoal]

theorem str83G4_torusInj_right_of_caseB
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hR : ¬ str83R L1 L2 S ≤ Q1 L1 L2 S) :
    ∀ x ∈ borelOf L1 S, Odd (orderOf x) →
      (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1 := by
  intro x hx hodd hcomm
  obtain ⟨hX, d, hB⟩ := str83G4_caseB_data hfr hR
  obtain ⟨u, hu, hux⟩ :=
    exists_conj_mem_of_hallTwoPrime_borelOf hfr.1.1.h1.sylow d.hD1hall hx hodd
  have huS : u ∈ S := hu.1
  have hSN : S ≤ Subgroup.normalizer (L2 : Set G) := hfr.1.1.h2.normalizes
  have hSNQ : S ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    hSN.trans (normalizer_le_normalizer_pCoreOf 2 L2)
  have hycomm : ∀ l ∈ L2,
      (u * x * u⁻¹) * l * (u * x * u⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := by
    intro l hl
    have huN : u⁻¹ ∈ Subgroup.normalizer (L2 : Set G) :=
      (Subgroup.normalizer (L2 : Set G)).inv_mem (hSN huS)
    have hl' : u⁻¹ * l * u ∈ L2 := by
      simpa using (Subgroup.mem_normalizer_iff.mp huN l).mp hl
    have h1 : u * (x * (u⁻¹ * l * u) * x⁻¹ * (u⁻¹ * l * u)⁻¹) * u⁻¹ ∈
        pCoreOf 2 L2 :=
      (Subgroup.mem_normalizer_iff.mp (hSNQ huS) _).mp (hcomm (u⁻¹ * l * u) hl')
    have heq : u * (x * (u⁻¹ * l * u) * x⁻¹ * (u⁻¹ * l * u)⁻¹) * u⁻¹ =
        (u * x * u⁻¹) * l * (u * x * u⁻¹)⁻¹ * l⁻¹ := by group
    rwa [heq] at h1
  have hy1 : u * x * u⁻¹ = 1 :=
    str83G4_eq_one_of_mem_d1_of_trivial_l2 hfr d hX hB (u * x * u⁻¹) hux hycomm
  calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
    _ = 1 := by rw [hy1]; group

theorem str83G4_eq_one_of_mem_d2_of_trivial_l1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∀ h ∈ d.D2, (∀ l ∈ L1, h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) → h = 1 := by
  intro h hh hcomm
  classical
  obtain ⟨hF, hBfr, ha, hSz, hL2, hZI⟩ := hfr
  have hfr : Str83G4Frame L1 L2 S a := ⟨hF, hBfr, ha, hSz, hL2, hZI⟩
  obtain ⟨hZ1eq, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hBfr ha hSz hL2 hZI
  have hhB : h ∈ bigB L1 L2 S :=
    (d.hD2hall.1.trans (le_sup_right.trans le_sup_left)) hh
  have hhP1 : h ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hhB
  have hhH : h ∈ L2 ⊔ S :=
    (le_sup_left : L2 ≤ L2 ⊔ S) (Subgroup.mem_inf.mp (d.hD2hall.1 hh)).1
  have hhNZ1 : h ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S) hhP1
  have hhNZ2 : h ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    bigB_le_normalizer_z2 L1 L2 S hhB
  have hhNX : h ∈ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    le_normalizer_str83X L1 L2 S hhP1
  have hhodd : Odd (orderOf h) :=
    Odd.of_dvd_nat d.hD2hall.2.1 (Subgroup.orderOf_dvd_natCard d.D2 hh)
  have hHNZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_z1 hfr
  have hHcentZ1 : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    str83G4_sup_le_centralizer_z1 hfr
  have hHNX : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_x hfr
  have hXH : str83X L1 L2 S ≤ L1 ⊔ S := str83G4_x_le_sup hfr
  have hhNZ1w : h ∈ Subgroup.normalizer
      (CFSG.conjugate (Z1 L1 L2 S) d.w : Set G) :=
    (str83G4_d1_sup_d2_le_normalizer hfr d).2.2.1 (Subgroup.mem_sup_right hh)
  have hhNXw : h ∈ Subgroup.normalizer
      (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) :=
    (str83G4_d1_sup_d2_le_normalizer hfr d).2.1 (Subgroup.mem_sup_right hh)
  have hhNI : h ∈ Subgroup.normalizer
      ((str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w : Subgroup G) : Set G) :=
    A4.mem_normalizer_inf hhNX hhNXw
  let I : Subgroup G := str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w
  let C : Subgroup G :=
    centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S) (Subgroup.zpowers h)
  have hCX : C ≤ str83X L1 L2 S := centralizerMod_le_left _ _ _
  have hI_le_X : I ≤ str83X L1 L2 S := inf_le_left
  have hnotI_Z2 : ¬ I ≤ Z2 L1 L2 S :=
    str83G4_not_x_inf_conjugate_x_le_z2 hfr d hX hB
  have hZ1C : Z1 L1 L2 S ≤ C := by
    intro z hz
    refine mem_centralizerMod.mpr ⟨str83G4_z1_le_x hfr hz, Subgroup.le_normalizer hz, ?_⟩
    intro u hu
    have hzpH : Subgroup.zpowers h ≤ P1 L1 L2 S :=
      Subgroup.zpowers_le.mpr ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hhB)
    have huN : u ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
      SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S) (hzpH hu)
    have h1 : u * z⁻¹ * u⁻¹ ∈ Z1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp huN z⁻¹).mp ((Z1 L1 L2 S).inv_mem hz)
    have h2 : z * (u * z⁻¹ * u⁻¹) ∈ Z1 L1 L2 S := (Z1 L1 L2 S).mul_mem hz h1
    simpa [mul_assoc] using h2
  have hCnorm : IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) C := by
    refine ⟨hCX, ?_⟩
    intro g hg z hz
    obtain ⟨hzX, -, hzComm⟩ := mem_centralizerMod.mp hz
    have hgNX : g ∈ Subgroup.normalizer (str83X L1 L2 S : Set G) := hHNX hg
    have hgNZ1 : g ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) := hHNZ1 hg
    have hxX : g * z * g⁻¹ ∈ str83X L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp hgNX z).mp hzX
    have hxH : g * z * g⁻¹ ∈ L1 ⊔ S := hXH hxX
    let q : G := h * g * h⁻¹ * g⁻¹
    have hqQ1 : q ∈ Q1 L1 L2 S :=
      str83G4_trivial_on_sup hfr hhB hcomm g hg
    let e : G := h * z * h⁻¹ * z⁻¹
    have heZ1 : e ∈ Z1 L1 L2 S := by
      have h1 := hzComm h (Subgroup.mem_zpowers h)
      have h2 : (z * h * z⁻¹ * h⁻¹)⁻¹ ∈ Z1 L1 L2 S := (Z1 L1 L2 S).inv_mem h1
      have heq : (z * h * z⁻¹ * h⁻¹)⁻¹ = e := by
        dsimp [e]
        group
      rwa [heq] at h2
    have hqe : h * g * h⁻¹ = q * g := by
      rw [show h * g * h⁻¹ = (h * g * h⁻¹ * g⁻¹) * g by group]
    have hze : h * z * h⁻¹ = e * z := by
      rw [show h * z * h⁻¹ = (h * z * h⁻¹ * z⁻¹) * z by group]
    have he_g : e * g = g * e :=
      Subgroup.mem_centralizer_iff.mp (hHcentZ1 hg) e heZ1
    have he_z : e * z = z * e :=
      Subgroup.mem_centralizer_iff.mp (hHcentZ1 (hXH hzX)) e heZ1
    have he_x : e * (g * z * g⁻¹) = (g * z * g⁻¹) * e :=
      Subgroup.mem_centralizer_iff.mp (hHcentZ1 hxH) e heZ1
    have hqH : q ∈ L1 ⊔ S :=
      (le_sup_right : S ≤ L1 ⊔ S) ((str83G4_q1_le_s hfr) hqQ1)
    have he_q : e * q = q * e :=
      Subgroup.mem_centralizer_iff.mp (hHcentZ1 hqH) e heZ1
    have hmain : h * (g * z * g⁻¹) * h⁻¹ = q * (e * (g * z * g⁻¹)) * q⁻¹ := by
      calc h * (g * z * g⁻¹) * h⁻¹
          = (h * g * h⁻¹) * (h * z * h⁻¹) * (h * g * h⁻¹)⁻¹ := by group
        _ = (q * g) * (e * z) * (q * g)⁻¹ := by rw [hqe, hze]
        _ = q * (e * (g * z * g⁻¹)) * q⁻¹ := by
          calc (q * g) * (e * z) * (q * g)⁻¹
              = q * (g * e) * z * g⁻¹ * q⁻¹ := by group
            _ = q * (e * g) * z * g⁻¹ * q⁻¹ := by rw [he_g.symm]
            _ = q * (e * (g * z * g⁻¹)) * q⁻¹ := by group
    have hxq : q * (g * z * g⁻¹) * q⁻¹ * (g * z * g⁻¹)⁻¹ ∈ Z1 L1 L2 S := by
      have h1 : ⁅g * z * g⁻¹, q⁆ ∈ ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ :=
        Subgroup.commutator_mem_commutator hxX hqQ1
      have h2 : ⁅g * z * g⁻¹, q⁆ ∈ Z1 L1 L2 S :=
        str83G4_commutator_x_q1_le hfr h1
      have h3 : (⁅g * z * g⁻¹, q⁆)⁻¹ ∈ Z1 L1 L2 S := (Z1 L1 L2 S).inv_mem h2
      have heq : (⁅g * z * g⁻¹, q⁆)⁻¹ =
          q * (g * z * g⁻¹) * q⁻¹ * (g * z * g⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rwa [heq] at h3
    have hres : h * (g * z * g⁻¹) * h⁻¹ * (g * z * g⁻¹)⁻¹ ∈ Z1 L1 L2 S := by
      rw [hmain]
      have heq : q * (e * (g * z * g⁻¹)) * q⁻¹ * (g * z * g⁻¹)⁻¹ =
          e * (q * (g * z * g⁻¹) * q⁻¹ * (g * z * g⁻¹)⁻¹) := by
        calc q * (e * (g * z * g⁻¹)) * q⁻¹ * (g * z * g⁻¹)⁻¹
            = (q * e) * (g * z * g⁻¹) * q⁻¹ * (g * z * g⁻¹)⁻¹ := by group
          _ = (e * q) * (g * z * g⁻¹) * q⁻¹ * (g * z * g⁻¹)⁻¹ := by rw [← he_q]
          _ = e * (q * (g * z * g⁻¹) * q⁻¹ * (g * z * g⁻¹)⁻¹) := by group
      rw [heq]
      exact (Z1 L1 L2 S).mul_mem heZ1 hxq
    have hx_comm_h : (g * z * g⁻¹) * h * (g * z * g⁻¹)⁻¹ * h⁻¹ ∈ Z1 L1 L2 S := by
      have h1 := (Z1 L1 L2 S).inv_mem hres
      have heq : (h * (g * z * g⁻¹) * h⁻¹ * (g * z * g⁻¹)⁻¹)⁻¹ =
          (g * z * g⁻¹) * h * (g * z * g⁻¹)⁻¹ * h⁻¹ := by group
      rwa [heq] at h1
    show g * z * g⁻¹ ∈ centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S)
      (Subgroup.zpowers h)
    exact (mem_centralizerMod_zpowers_iff_of_normalizer
      (N := str83X L1 L2 S) (L := Z1 L1 L2 S) (t := h)
      (hXH.trans hHNZ1) hhNZ1 hxX).mpr hx_comm_h
  have hCneZ1 : C ≠ Z1 L1 L2 S := by
    intro hCZ
    have hI2 : IsPGroup 2 I := hX.isPGroup.to_le hI_le_X
    let A : Subgroup G := Subgroup.zpowers h
    have hAN : A ≤ Subgroup.normalizer (I : Set G) := Subgroup.zpowers_le.mpr hhNI
    have hAcard : Nat.card ↥A = orderOf h := by
      change Nat.card ↥(Subgroup.zpowers h) = orderOf h
      rw [Nat.card_zpowers]
    have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥I) := by
      obtain ⟨k, hk⟩ := hI2.exists_card_eq
      rw [hAcard, hk]
      exact (Nat.coprime_two_left.mpr hhodd).symm.pow_right k
    have hsolv : Group.IsSolvable ↥I := by
      have := hI2.isNilpotent
      infer_instance
    have hcommI : ⁅I, A⁆ ≤ Z2 L1 L2 S := by
      refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem hhNZ2 ?_
      intro a haI
      have h1 := str83G4_commutator_mem_z2_of_mem_x_inf_conjugate hfr d hX hB h hhH a haI
      have h2 : (h * a * h⁻¹ * a⁻¹)⁻¹ ∈ Z2 L1 L2 S := (Z2 L1 L2 S).inv_mem h1
      have heq : (h * a * h⁻¹ * a⁻¹)⁻¹ = ⁅a, h⁆ := by
        rw [commutatorElement_def]
        group
      rwa [heq] at h2
    have hI_union : I ≤ Z2 L1 L2 S ⊔ (I ⊓ Subgroup.centralizer (A : Set G)) := by
      have hle := CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite
        (R := I) (A := A) hAN hcop hsolv
      refine hle.trans ?_
      exact sup_le (hcommI.trans le_sup_left) le_sup_right
    have hsubC : I ⊓ Subgroup.centralizer (A : Set G) ≤ C := by
      intro c hc
      have hcX : c ∈ str83X L1 L2 S := hI_le_X hc.1
      have hcu : c * h = h * c :=
        (Subgroup.mem_centralizer_iff.mp hc.2 h
          (show h ∈ A from Subgroup.mem_zpowers h)).symm
      have hch : c * h * c⁻¹ * h⁻¹ ∈ Z1 L1 L2 S := by
        rw [hcu]
        have h1 : h * c * c⁻¹ * h⁻¹ = 1 := by group
        rw [h1]
        exact (Z1 L1 L2 S).one_mem
      show c ∈ centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S) (Subgroup.zpowers h)
      exact (mem_centralizerMod_zpowers_iff_of_normalizer
        (N := str83X L1 L2 S) (L := Z1 L1 L2 S) (t := h)
        (hXH.trans hHNZ1) hhNZ1 hcX).mpr hch
    have hnotCA : ¬ (I ⊓ Subgroup.centralizer (A : Set G)) ≤ Z1 L1 L2 S := by
      intro hle
      exact hnotI_Z2 (hI_union.trans (sup_le le_rfl (hle.trans hZ1Z2)))
    exact hnotCA (hsubC.trans (le_of_eq hCZ))
  have hstep := str83G4_isChiefStep_x_z1 hfr d hX hB
  have hCeq : C = str83X L1 L2 S := by
    rcases hstep.2.2.2 C hCnorm hZ1C hCX with hCZ | hCXeq
    · exact absurd hCZ hCneZ1
    · exact hCXeq
  have hZ1w_le_Z2 : CFSG.conjugate (Z1 L1 L2 S) d.w ≤ Z2 L1 L2 S := by
    calc CFSG.conjugate (Z1 L1 L2 S) d.w
        ≤ CFSG.conjugate (Z2 L1 L2 S) d.w := Subgroup.map_mono hZ1Z2
      _ = Z2 L1 L2 S := str83G4_conjugate_z2_eq hfr d
  have hcentZ1w : ∀ z ∈ CFSG.conjugate (Z1 L1 L2 S) d.w, h * z = z * h := by
    intro z hz
    have hzZ2 : z ∈ Z2 L1 L2 S := hZ1w_le_Z2 hz
    have hzX : z ∈ str83X L1 L2 S := z2_le_str83X L1 L2 S hzZ2
    have hzC : z ∈ C := by
      rw [hCeq]
      exact hzX
    have hmem : h * z * h⁻¹ * z⁻¹ ∈
        Z1 L1 L2 S ⊓ CFSG.conjugate (Z1 L1 L2 S) d.w := by
      refine ⟨?_, ?_⟩
      · have h1 := (mem_centralizerMod.mp hzC).2.2 h (Subgroup.mem_zpowers h)
        have h2 : (z * h * z⁻¹ * h⁻¹)⁻¹ ∈ Z1 L1 L2 S := (Z1 L1 L2 S).inv_mem h1
        have heq : (z * h * z⁻¹ * h⁻¹)⁻¹ = h * z * h⁻¹ * z⁻¹ := by group
        rwa [heq] at h2
      · have h1 : h * z * h⁻¹ ∈ CFSG.conjugate (Z1 L1 L2 S) d.w :=
          (Subgroup.mem_normalizer_iff.mp hhNZ1w z).mp hz
        exact (CFSG.conjugate (Z1 L1 L2 S) d.w).mul_mem h1
          ((CFSG.conjugate (Z1 L1 L2 S) d.w).inv_mem hz)
    have hone : h * z * h⁻¹ * z⁻¹ = 1 := by
      have hbot := hmem
      rw [str83G4_z1_inf_conjugate_w hfr d] at hbot
      exact Subgroup.mem_bot.mp hbot
    calc h * z = (h * z * h⁻¹ * z⁻¹) * (z * h) := by group
      _ = z * h := by rw [hone, one_mul]
  have hcentZ1 : ∀ z ∈ Z1 L1 L2 S, h * z = z * h := by
    intro z hz
    have hzw : d.w⁻¹ * z * d.w ∈ CFSG.conjugate (Z1 L1 L2 S) d.w := by
      rw [CFSG.mem_conjugate_iff]
      have heq : d.w * (d.w⁻¹ * z * d.w) * d.w⁻¹ = z := by group
      rw [heq]
      exact hz
    have h1 := hcentZ1w _ hzw
    have h2 : d.w * h * d.w⁻¹ = h⁻¹ := d.hwInv h hh
    have hconj : h⁻¹ * z = z * h⁻¹ := by
      have h3 := congrArg (fun t => d.w * t * d.w⁻¹) h1
      rw [show d.w * (h * (d.w⁻¹ * z * d.w)) * d.w⁻¹ =
          (d.w * h * d.w⁻¹) * z by group] at h3
      rw [show d.w * ((d.w⁻¹ * z * d.w) * h) * d.w⁻¹ =
          z * (d.w * h * d.w⁻¹) by group] at h3
      rw [h2] at h3
      exact h3
    calc h * z = (h * z * h⁻¹) * h := by group
      _ = z * h := by
        have h4 : h * z * h⁻¹ = z := by
          calc h * z * h⁻¹ = h * (z * h⁻¹) := by group
            _ = h * (h⁻¹ * z) := by rw [hconj]
            _ = z := by group
        rw [h4]
  have hcentOmega : ∀ z ∈ omegaOneCenterOf S, h * z = z * h := by
    intro z hz
    rw [← hZ1eq] at hz
    exact hcentZ1 z hz
  exact str83G4_torusFaithful hfr h (d.hD2hall.1 hh) hhodd hcentOmega

theorem str83G4_torusInj_left_of_caseB
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hR : ¬ str83R L1 L2 S ≤ Q1 L1 L2 S) :
    ∀ x ∈ borelOf L2 S, Odd (orderOf x) →
      (∀ l ∈ L1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) → x = 1 := by
  intro x hx hodd hcomm
  obtain ⟨hX, d, hB⟩ := str83G4_caseB_data hfr hR
  obtain ⟨u, hu, hux⟩ :=
    exists_conj_mem_of_hallTwoPrime_borelOf hfr.1.1.h2.sylow d.hD2hall hx hodd
  have huS : u ∈ S := hu.1
  have hSN : S ≤ Subgroup.normalizer (L1 : Set G) := hfr.1.1.h1.normalizes
  have hSNQ : S ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    hSN.trans (normalizer_le_normalizer_pCoreOf 2 L1)
  have hycomm : ∀ l ∈ L1,
      (u * x * u⁻¹) * l * (u * x * u⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1 := by
    intro l hl
    have huN : u⁻¹ ∈ Subgroup.normalizer (L1 : Set G) :=
      (Subgroup.normalizer (L1 : Set G)).inv_mem (hSN huS)
    have hl' : u⁻¹ * l * u ∈ L1 := by
      simpa using (Subgroup.mem_normalizer_iff.mp huN l).mp hl
    have h1 : u * (x * (u⁻¹ * l * u) * x⁻¹ * (u⁻¹ * l * u)⁻¹) * u⁻¹ ∈
        pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp (hSNQ huS) _).mp (hcomm (u⁻¹ * l * u) hl')
    have heq : u * (x * (u⁻¹ * l * u) * x⁻¹ * (u⁻¹ * l * u)⁻¹) * u⁻¹ =
        (u * x * u⁻¹) * l * (u * x * u⁻¹)⁻¹ * l⁻¹ := by group
    rwa [heq] at h1
  have hy1 : u * x * u⁻¹ = 1 :=
    str83G4_eq_one_of_mem_d2_of_trivial_l1 hfr d hX hB (u * x * u⁻¹) hux hycomm
  calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
    _ = 1 := by rw [hy1]; group

theorem str83TorusInj_of_caseAFalse
    (hRq : Str83RqEq) (hA : Str83G4CaseAFalse) :
    Str83TorusInj := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  have hL2q : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) :=
    hRq G L1 L2 S a hF ha hSz hBig hL2
  have hfr : Str83G4Frame L1 L2 S a := str83G4Frame_of hF ha hSz hL2q
  refine ⟨?_, ?_⟩
  · intro d hd hodd hcomm
    by_cases hR : str83R L1 L2 S ≤ Q1 L1 L2 S
    · exact (hA G L1 L2 S a hfr hR).elim
    · exact str83G4_torusInj_left_of_caseB hfr hR d hd hodd hcomm
  · intro d hd hodd hcomm
    by_cases hR : str83R L1 L2 S ≤ Q1 L1 L2 S
    · exact (hA G L1 L2 S a hfr hR).elim
    · exact str83G4_torusInj_right_of_caseB hfr hR d hd hodd hcomm

end CFSG.Quasithin.Stroth

end
