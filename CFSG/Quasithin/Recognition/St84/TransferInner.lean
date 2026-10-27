module

public import CFSG.Quasithin.Recognition.St84.TransferSetup
public import CFSG.GroupTheory.InnerOfFixSylowTwo
public import CFSG.GroupTheory.CenterOfSelfCentralizing

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def f112saW (L1 L2 S : Subgroup H) : Subgroup H :=
  centerOf (S ⊓ f112saK L1 L2 S) ⊓ Subgroup.centralizer (f112saK L1 L2 S : Set H)

theorem f112saK_le_P1' (L1 L2 S : Subgroup H) :
    f112saK L1 L2 S ≤ f112saP1' L1 L2 S := by
  rw [f112saK, f112saP1']
  exact sup_le ((f112sa_X1_le_oTwoRes L1 L2 S).trans le_sup_left) le_sup_right

theorem f112saK_le_P2' (L1 L2 S : Subgroup H) :
    f112saK L1 L2 S ≤ f112saP2' L1 L2 S := by
  rw [f112saK, f112saP2']
  exact sup_le le_sup_right ((f112sa_X2_le_oTwoRes L1 L2 S).trans le_sup_left)

theorem f112sa_exists_center_conj_eq_P1'_of_hyp111R
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) {c : H}
    (hcB : c ∈ bigB L1 L2 S)
    (hcT : ∀ t ∈ S ⊓ f112saK L1 L2 S, c * t = t * c) :
    ∃ z ∈ centerOf (S ⊓ f112saK L1 L2 S),
      ∀ x ∈ f112saP1' L1 L2 S, c * x * c⁻¹ = z * x * z⁻¹ := by
  have hTle : S ⊓ f112saK L1 L2 S ≤ f112saP1' L1 L2 S :=
    inf_le_right.trans (f112saK_le_P1' L1 L2 S)
  have hQn : ((pCoreOf 2 (f112saP1' L1 L2 S)).subgroupOf
      (f112saP1' L1 L2 S)).Normal := by
    have e : (pCoreOf 2 (f112saP1' L1 L2 S)).subgroupOf (f112saP1' L1 L2 S) =
        CFSG.pCore 2 ↥(f112saP1' L1 L2 S) := by
      show (Subgroup.map (f112saP1' L1 L2 S).subtype
        (CFSG.pCore 2 ↥(f112saP1' L1 L2 S))).comap
          (f112saP1' L1 L2 S).subtype = _
      exact Subgroup.comap_map_eq_self_of_injective
        (f112saP1' L1 L2 S).subtype_injective _
    rw [e]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have hgX : c ∈ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    f112sa_P1_le_normalizer_P1' hF
      ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) hcB)
  have hTodd : Odd ((S ⊓ f112saK L1 L2 S).subgroupOf (f112saP1' L1 L2 S)).index :=
    Nat.not_even_iff_odd.mp fun he =>
      (f112sa_T_sylow_P1'_of_hyp111R hF hR).2.2 (even_iff_two_dvd.mp he)
  obtain ⟨z, hz, hzconj⟩ :=
    CFSG.GroupTheory.exists_mem_center_sylow_two_conj_eq
      (Y := H) (X := f112saP1' L1 L2 S) (Q := pCoreOf 2 (f112saP1' L1 L2 S))
      (T := S ⊓ f112saK L1 L2 S)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hQn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (f112sa_charTwo_P1'_of_hyp111R hF hR) hTle
      (f112sa_T_sylow_P1'_of_hyp111R hF hR).2.1 hTodd hgX hcT
  exact ⟨z, hz, hzconj⟩

theorem f112sa_exists_center_conj_eq_P1'
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) {c : H}
    (hcB : c ∈ bigB L1 L2 S)
    (hcT : ∀ t ∈ S ⊓ f112saK L1 L2 S, c * t = t * c) :
    ∃ z ∈ centerOf (S ⊓ f112saK L1 L2 S),
      ∀ x ∈ f112saP1' L1 L2 S, c * x * c⁻¹ = z * x * z⁻¹ :=
  f112sa_exists_center_conj_eq_P1'_of_hyp111R hF.toW
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1) hcB hcT

theorem f112sa_exists_center_conj_eq_P2'_of_hyp111R
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) {c : H}
    (hcB : c ∈ bigB L1 L2 S)
    (hcT : ∀ t ∈ S ⊓ f112saK L1 L2 S, c * t = t * c) :
    ∃ z ∈ centerOf (S ⊓ f112saK L1 L2 S),
      ∀ x ∈ f112saP2' L1 L2 S, c * x * c⁻¹ = z * x * z⁻¹ := by
  have hTle : S ⊓ f112saK L1 L2 S ≤ f112saP2' L1 L2 S :=
    inf_le_right.trans (f112saK_le_P2' L1 L2 S)
  have hQn : ((pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf
      (f112saP2' L1 L2 S)).Normal := by
    have e : (pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf (f112saP2' L1 L2 S) =
        CFSG.pCore 2 ↥(f112saP2' L1 L2 S) := by
      show (Subgroup.map (f112saP2' L1 L2 S).subtype
        (CFSG.pCore 2 ↥(f112saP2' L1 L2 S))).comap
          (f112saP2' L1 L2 S).subtype = _
      exact Subgroup.comap_map_eq_self_of_injective
        (f112saP2' L1 L2 S).subtype_injective _
    rw [e]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have hgX : c ∈ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    f112sa_P2_le_normalizer_P2' hF
      ((le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S) hcB)
  have hTodd : Odd ((S ⊓ f112saK L1 L2 S).subgroupOf (f112saP2' L1 L2 S)).index :=
    Nat.not_even_iff_odd.mp fun he =>
      (f112sa_T_sylow_P2'_of_hyp111R hF hR).2.2 (even_iff_two_dvd.mp he)
  obtain ⟨z, hz, hzconj⟩ :=
    CFSG.GroupTheory.exists_mem_center_sylow_two_conj_eq
      (Y := H) (X := f112saP2' L1 L2 S) (Q := pCoreOf 2 (f112saP2' L1 L2 S))
      (T := S ⊓ f112saK L1 L2 S)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hQn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (f112sa_charTwo_P2'_of_hyp111R hF hR) hTle
      (f112sa_T_sylow_P2'_of_hyp111R hF hR).2.1 hTodd hgX hcT
  exact ⟨z, hz, hzconj⟩

theorem f112sa_inv_mul_mem_W {L1 L2 S : Subgroup H} {c z z' : H}
    (hz : z ∈ centerOf (S ⊓ f112saK L1 L2 S))
    (hz' : z' ∈ centerOf (S ⊓ f112saK L1 L2 S))
    (hzc : ∀ x ∈ f112saP1' L1 L2 S, c * x * c⁻¹ = z * x * z⁻¹)
    (hz'c : ∀ x ∈ f112saP2' L1 L2 S, c * x * c⁻¹ = z' * x * z'⁻¹) :
    z⁻¹ * z' ∈ f112saW L1 L2 S := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (S ⊓ f112saK L1 L2 S).mul_mem
        ((S ⊓ f112saK L1 L2 S).inv_mem hz.1) hz'.1
    · exact (Subgroup.centralizer ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H)).mul_mem
        ((Subgroup.centralizer ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H)).inv_mem hz.2)
        hz'.2
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk1 : k ∈ f112saP1' L1 L2 S := f112saK_le_P1' L1 L2 S hk
    have hk2 : k ∈ f112saP2' L1 L2 S := f112saK_le_P2' L1 L2 S hk
    have hEq : z * k * z⁻¹ = z' * k * z'⁻¹ := (hzc k hk1).symm.trans (hz'c k hk2)
    have ha : z⁻¹ * z' * k * (z⁻¹ * z')⁻¹ = k := by
      calc z⁻¹ * z' * k * (z⁻¹ * z')⁻¹
          = z⁻¹ * (z' * k * z'⁻¹) * z := by group
        _ = z⁻¹ * (z * k * z⁻¹) * z := by rw [← hEq]
        _ = k := by group
    exact (mul_inv_eq_iff_eq_mul.mp ha).symm

theorem f112sa_bigB_inf_centralizer_eq_centerOf_of_W_eq_bot_of_hyp111R
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    (hW : f112saW L1 L2 S = ⊥) :
    bigB L1 L2 S ⊓ Subgroup.centralizer (S ⊓ f112saK L1 L2 S : Set H) =
      centerOf (S ⊓ f112saK L1 L2 S) := by
  have hTB : S ⊓ f112saK L1 L2 S ≤ bigB L1 L2 S :=
    (inf_le_left : S ⊓ f112saK L1 L2 S ≤ S).trans
      (le_sup_right : S ≤ bigB L1 L2 S)
  refine le_antisymm ?_ ?_
  · rintro c ⟨hcB, hcC⟩
    have hcT : ∀ t ∈ S ⊓ f112saK L1 L2 S, c * t = t * c :=
      fun t ht => (Subgroup.mem_centralizer_iff.mp hcC t ht).symm
    obtain ⟨z, hz, hzc⟩ := f112sa_exists_center_conj_eq_P1'_of_hyp111R hF hR hcB hcT
    obtain ⟨z', hz', hz'c⟩ := f112sa_exists_center_conj_eq_P2'_of_hyp111R hF hR hcB hcT
    have hzz' : z⁻¹ * z' ∈ f112saW L1 L2 S := f112sa_inv_mul_mem_W hz hz' hzc hz'c
    have hzz'1 : z⁻¹ * z' = 1 := by
      have hmem : z⁻¹ * z' ∈ f112saW L1 L2 S := hzz'
      rw [hW] at hmem
      simpa using hmem
    have hz'eq : z' = z := (inv_mul_eq_one.mp hzz'1).symm
    have hzc2 : ∀ x ∈ f112saP2' L1 L2 S, c * x * c⁻¹ = z * x * z⁻¹ := by
      intro x hx
      rw [hz'eq] at hz'c
      exact hz'c x hx
    have hmemC : ∀ (E : Subgroup H) {z : H}, z ∈ centerOf (S ⊓ f112saK L1 L2 S) →
        (∀ x ∈ E, c * x * c⁻¹ = z * x * z⁻¹) →
        c * z⁻¹ ∈ Subgroup.centralizer (E : Set H) := by
      intro E z hz hEq
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hcz : Commute z c := (hcT z hz.1).symm
      have hza : z⁻¹ * c = c * z⁻¹ := hcz.inv_left.eq
      have hx' : z⁻¹ * c * x * (z⁻¹ * c)⁻¹ = x := by
        calc z⁻¹ * c * x * (z⁻¹ * c)⁻¹
            = z⁻¹ * (c * x * c⁻¹) * z := by group
          _ = z⁻¹ * (z * x * z⁻¹) * z := by rw [hEq x hx]
          _ = x := by group
      have hcomm : z⁻¹ * c * x = x * (z⁻¹ * c) := mul_inv_eq_iff_eq_mul.mp hx'
      rw [← hza]
      exact hcomm.symm
    have hczB : c * z⁻¹ ∈ bigB L1 L2 S :=
      (bigB L1 L2 S).mul_mem hcB
        ((bigB L1 L2 S).inv_mem (hTB hz.1))
    have hczE1 : c * z⁻¹ ∈ Subgroup.centralizer (f112saP1' L1 L2 S : Set H) :=
      hmemC (f112saP1' L1 L2 S) hz hzc
    have hczE2 : c * z⁻¹ ∈ Subgroup.centralizer (f112saP2' L1 L2 S : Set H) :=
      hmemC (f112saP2' L1 L2 S) hz hzc2
    have hcore : c * z⁻¹ ∈ bigB L1 L2 S ⊓
        Subgroup.centralizer (f112saP1' L1 L2 S : Set H) ⊓
          Subgroup.centralizer (f112saP2' L1 L2 S : Set H) :=
      ⟨⟨hczB, hczE1⟩, hczE2⟩
    rw [f112sa_core_free_of_hyp111R hF hR] at hcore
    have hc1 : c * z⁻¹ = 1 := by simpa using hcore
    have hceq : c = z := mul_inv_eq_one.mp hc1
    rw [hceq]
    exact hz
  · intro z hz
    exact Subgroup.mem_inf.mpr ⟨(le_sup_right : S ≤ bigB L1 L2 S) hz.1.1, hz.2⟩

theorem f112sa_S_inf_centralizer_le_T_of_W_eq_bot_of_hyp111R
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    (hW : f112saW L1 L2 S = ⊥) :
    S ⊓ Subgroup.centralizer (S ⊓ f112saK L1 L2 S : Set H) ≤
      S ⊓ f112saK L1 L2 S := by
  intro x hx
  have hx' : x ∈ bigB L1 L2 S ⊓
      Subgroup.centralizer (S ⊓ f112saK L1 L2 S : Set H) :=
    ⟨(le_sup_right : S ≤ bigB L1 L2 S) hx.1, hx.2⟩
  rw [f112sa_bigB_inf_centralizer_eq_centerOf_of_W_eq_bot_of_hyp111R hF hR hW] at hx'
  exact hx'.1

theorem f112sa_S_inf_centralizer_le_T_of_W_eq_bot
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S)
    (hW : f112saW L1 L2 S = ⊥) :
    S ⊓ Subgroup.centralizer (S ⊓ f112saK L1 L2 S : Set H) ≤
      S ⊓ f112saK L1 L2 S :=
  f112sa_S_inf_centralizer_le_T_of_W_eq_bot_of_hyp111R hF
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1) hW

theorem f112saW_eq_bot_of_centerOf_inf_centralizer_le_of_hyp111R
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) {k1 k2 : H}
    (hk1 : k1 ∈ f112saK L1 L2 S) (hk2 : k2 ∈ f112saK L1 L2 S)
    (h1 : centerOf (S ⊓ f112saK L1 L2 S) ⊓
      Subgroup.centralizer ({k1} : Set H) ≤ Subgroup.centralizer (oTwoRes L1 : Set H))
    (h2 : centerOf (S ⊓ f112saK L1 L2 S) ⊓
      Subgroup.centralizer ({k2} : Set H) ≤ Subgroup.centralizer (oTwoRes L2 : Set H)) :
    f112saW L1 L2 S = ⊥ := by
  have hWleZ : f112saW L1 L2 S ≤ centerOf (S ⊓ f112saK L1 L2 S) := inf_le_left
  have hWleK : f112saW L1 L2 S ≤
      Subgroup.centralizer (f112saK L1 L2 S : Set H) := inf_le_right
  have hleCk1 : Subgroup.centralizer (f112saK L1 L2 S : Set H) ≤
      Subgroup.centralizer ({k1} : Set H) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk1)
  have hleCk2 : Subgroup.centralizer (f112saK L1 L2 S : Set H) ≤
      Subgroup.centralizer ({k2} : Set H) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk2)
  have hWleO1 : f112saW L1 L2 S ≤ Subgroup.centralizer (oTwoRes L1 : Set H) :=
    (le_inf hWleZ (hWleK.trans hleCk1)).trans h1
  have hWleO2 : f112saW L1 L2 S ≤ Subgroup.centralizer (oTwoRes L2 : Set H) :=
    (le_inf hWleZ (hWleK.trans hleCk2)).trans h2
  have hX1leK : f112saX1 L1 L2 S ≤ f112saK L1 L2 S := fun x hx => Subgroup.mem_sup_left hx
  have hX2leK : f112saX2 L1 L2 S ≤ f112saK L1 L2 S := fun x hx => Subgroup.mem_sup_right hx
  have hWleCX1 : f112saW L1 L2 S ≤
      Subgroup.centralizer (f112saX1 L1 L2 S : Set H) :=
    hWleK.trans (Subgroup.centralizer_le hX1leK)
  have hWleCX2 : f112saW L1 L2 S ≤
      Subgroup.centralizer (f112saX2 L1 L2 S : Set H) :=
    hWleK.trans (Subgroup.centralizer_le hX2leK)
  have hE1leCW : f112saP1' L1 L2 S ≤
      Subgroup.centralizer (f112saW L1 L2 S : Set H) := by
    rw [f112saP1']
    exact sup_le (Subgroup.le_centralizer_iff.mp hWleO1)
      (Subgroup.le_centralizer_iff.mp hWleCX2)
  have hE2leCW : f112saP2' L1 L2 S ≤
      Subgroup.centralizer (f112saW L1 L2 S : Set H) := by
    rw [f112saP2']
    exact sup_le (Subgroup.le_centralizer_iff.mp hWleO2)
      (Subgroup.le_centralizer_iff.mp hWleCX1)
  have hWleE1 : f112saW L1 L2 S ≤
      Subgroup.centralizer (f112saP1' L1 L2 S : Set H) :=
    Subgroup.le_centralizer_iff.mpr hE1leCW
  have hWleE2 : f112saW L1 L2 S ≤
      Subgroup.centralizer (f112saP2' L1 L2 S : Set H) :=
    Subgroup.le_centralizer_iff.mpr hE2leCW
  have hWleB : f112saW L1 L2 S ≤ bigB L1 L2 S :=
    hWleZ.trans ((inf_le_left : centerOf (S ⊓ f112saK L1 L2 S) ≤
      S ⊓ f112saK L1 L2 S).trans ((inf_le_left : S ⊓ f112saK L1 L2 S ≤ S).trans
        (le_sup_right : S ≤ bigB L1 L2 S)))
  have hcore : f112saW L1 L2 S ≤ bigB L1 L2 S ⊓
      Subgroup.centralizer (f112saP1' L1 L2 S : Set H) ⊓
        Subgroup.centralizer (f112saP2' L1 L2 S : Set H) :=
    le_inf (le_inf hWleB hWleE1) hWleE2
  rw [f112sa_core_free_of_hyp111R hF hR] at hcore
  exact le_bot_iff.mp hcore

theorem f112saW_eq_bot_of_centerOf_inf_centralizer_le
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) {k1 k2 : H}
    (hk1 : k1 ∈ f112saK L1 L2 S) (hk2 : k2 ∈ f112saK L1 L2 S)
    (h1 : centerOf (S ⊓ f112saK L1 L2 S) ⊓
      Subgroup.centralizer ({k1} : Set H) ≤ Subgroup.centralizer (oTwoRes L1 : Set H))
    (h2 : centerOf (S ⊓ f112saK L1 L2 S) ⊓
      Subgroup.centralizer ({k2} : Set H) ≤ Subgroup.centralizer (oTwoRes L2 : Set H)) :
    f112saW L1 L2 S = ⊥ :=
  f112saW_eq_bot_of_centerOf_inf_centralizer_le_of_hyp111R hF
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1) hk1 hk2 h1 h2

theorem f112sa_centerOf_T_le_P1'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    centerOf (S ⊓ f112saK L1 L2 S) ≤ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) :=
  CFSG.GroupTheory.inf_centralizer_le_inf_centralizer_of_le
    (inf_le_right.trans (f112saK_le_P1' L1 L2 S))
    (F7.isSylowTwoOf_pCoreOf_le (f112sa_T_sylow_P1'_of_hyp111R hF hR))
    (f112sa_charTwo_P1'_of_hyp111R hF hR)

theorem f112sa_centerOf_T_le_P1' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    centerOf (S ⊓ f112saK L1 L2 S) ≤ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) :=
  f112sa_centerOf_T_le_P1'_of_hyp111R hF.toW (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_centerOf_T_le_P2'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    centerOf (S ⊓ f112saK L1 L2 S) ≤ centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) :=
  CFSG.GroupTheory.inf_centralizer_le_inf_centralizer_of_le
    (inf_le_right.trans (f112saK_le_P2' L1 L2 S))
    (F7.isSylowTwoOf_pCoreOf_le (f112sa_T_sylow_P2'_of_hyp111R hF hR))
    (f112sa_charTwo_P2'_of_hyp111R hF hR)

theorem f112sa_centerOf_T_le_P2' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    centerOf (S ⊓ f112saK L1 L2 S) ≤ centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) :=
  f112sa_centerOf_T_le_P2'_of_hyp111R hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_centerOf_inf_centralizer_le_of_pCoreOf_P1'_of_hyp111R
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) {k : H}
    (h : pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L1 : Set H)) :
    centerOf (S ⊓ f112saK L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L1 : Set H) :=
  (inf_le_inf ((f112sa_centerOf_T_le_P1'_of_hyp111R hF hR).trans inf_le_left) le_rfl).trans h

theorem f112sa_centerOf_inf_centralizer_le_of_pCoreOf_P1'
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) {k : H}
    (h : pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L1 : Set H)) :
    centerOf (S ⊓ f112saK L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L1 : Set H) :=
  f112sa_centerOf_inf_centralizer_le_of_pCoreOf_P1'_of_hyp111R hF
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1) h

theorem f112sa_centerOf_inf_centralizer_le_of_pCoreOf_P2'_of_hyp111R
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) {k : H}
    (h : pCoreOf 2 (f112saP2' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L2 : Set H)) :
    centerOf (S ⊓ f112saK L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L2 : Set H) :=
  (inf_le_inf ((f112sa_centerOf_T_le_P2'_of_hyp111R hF hR).trans inf_le_left) le_rfl).trans h

theorem f112sa_centerOf_inf_centralizer_le_of_pCoreOf_P2'
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) {k : H}
    (h : pCoreOf 2 (f112saP2' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L2 : Set H)) :
    centerOf (S ⊓ f112saK L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L2 : Set H) :=
  f112sa_centerOf_inf_centralizer_le_of_pCoreOf_P2'_of_hyp111R hF
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1) h

end CFSG.Quasithin.F112R.St84
