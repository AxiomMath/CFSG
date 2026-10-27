module

public import CFSG.Quasithin.Vol2.KGFactJ4M4GenTop
public import CFSG.Quasithin.Vol2.KGFactJ4M4GenPC
public import CFSG.Quasithin.Vol2.KGFactJ4M4GenFix
public import CFSG.Quasithin.Vol2.KGFactJ4BlockTL
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4C

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L52

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin.B5.Ln (mat)
open CFSG.Quasithin.KGC31.J4M4.Gen (z1Elt cElt closure_w1_w2_c_eq_top)
open scoped Matrix

theorem sup_perfectCore_eq_top_of_sylow
    {S : Subgroup J} (hS : IsSylowTwoOf S CFSG.Quasithin.KGJ4.M4) {z : J}
    (hzF : z ∈ F4 j4Facts.mat chkF_true) (hz1 : z ≠ 1)
    (hzS : z ∈ Subgroup.centralizer (S : Set J)) :
    CFSG.Quasithin.KGJ4.M4 ⊔ perfectCore (Subgroup.centralizer ({z} : Set J)) = ⊤ := by
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_z0 hS hzF hz1 hzS
  obtain ⟨m, hmM, hzm⟩ := exists_M4_conj_z1 hS hzF hz1 hzS
  have hz1c : ∃ g' : J, z1Elt = g' * CFSG.Quasithin.J4Loc.z0 * g'⁻¹ := by
    refine ⟨m⁻¹ * g, ?_⟩
    have e : z1Elt = m⁻¹ * z * m := by rw [hzm]; group
    rw [e, hg]
    group
  have hP : cElt ∈ perfectCore (Subgroup.centralizer ({z1Elt} : Set J)) :=
    c_mem_perfectCore hz1c
  have htop1 : CFSG.Quasithin.KGJ4.M4 ⊔ perfectCore (Subgroup.centralizer ({z1Elt} : Set J)) =
      ⊤ := by
    rw [eq_top_iff, ← closure_w1_w2_c_eq_top]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left CFSG.Quasithin.KGJ4.w1_mem_M4
    · exact Subgroup.mem_sup_left CFSG.Quasithin.KGJ4.w2_mem_M4
    · exact Subgroup.mem_sup_right hP
  set ψ := (MulAut.conj m).toMonoidHom with hψ
  have e1 : perfectCore (Subgroup.centralizer ({z} : Set J)) =
      (perfectCore (Subgroup.centralizer ({z1Elt} : Set J))).map ψ := by
    rw [map_perfectCore, hψ, CFSG.Quasithin.H13.J4.map_centralizer_singleton, MulAut.conj_apply,
      ← hzm]
  have hMψ : CFSG.Quasithin.KGJ4.M4.map ψ = CFSG.Quasithin.KGJ4.M4 := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact CFSG.Quasithin.KGJ4.M4.mul_mem (CFSG.Quasithin.KGJ4.M4.mul_mem hmM hx)
        (CFSG.Quasithin.KGJ4.M4.inv_mem hmM)
    · intro x hx
      refine ⟨m⁻¹ * x * m, CFSG.Quasithin.KGJ4.M4.mul_mem
        (CFSG.Quasithin.KGJ4.M4.mul_mem (CFSG.Quasithin.KGJ4.M4.inv_mem hmM) hx) hmM, ?_⟩
      simp only [hψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have e2 : CFSG.Quasithin.KGJ4.M4 ⊔ (perfectCore (Subgroup.centralizer ({z1Elt} : Set J))).map ψ =
      (CFSG.Quasithin.KGJ4.M4 ⊔ perfectCore (Subgroup.centralizer ({z1Elt} : Set J))).map ψ := by
    rw [Subgroup.map_sup, hMψ]
  have hsurj : Function.Surjective ψ := fun x => ⟨m⁻¹ * x * m, by
    simp only [hψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩
  rw [e1, e2, htop1, Subgroup.map_top_of_surjective _ hsurj]

theorem modelL52_M4_gen :
    ModelL52 J (fun Y => Y ≤ CFSG.Quasithin.KGJ4.M4) := by
  intro Y V S z hYM hYq hV hV1 hS hzV hz1 hzS
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  obtain ⟨hYeq, hO⟩ := eq_M4_of_le hYM hYq hV hV1
  subst hYeq
  have hzF : z ∈ F4 j4Facts.mat chkF_true := by
    have := (hV hzV).1
    rwa [hO] at this
  obtain ⟨g, hg⟩ := exists_conj_z0 hS hzF hz1 hzS
  set φ := (MulAut.conj g).toMonoidHom with hφ
  have hB : perfectCore (Subgroup.centralizer ({z} : Set J)) = J4M2.B0grp.map φ := by
    have h1 : Subgroup.centralizer ({z} : Set J) =
        (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map φ := by
      rw [hφ, J4.map_centralizer_singleton, MulAut.conj_apply, hg]
    rw [h1, ← map_perfectCore, show Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J) =
      J4M2.M2 from rfl, JM.perfectCore_M2 hF]
  have hhat : IsHat (↥(J4M2.B0grp.map φ) ⧸ CFSG.pCore 2 ↥(J4M2.B0grp.map φ))
      (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    isHat_map_conj g (JM.isHat_B0grp hF)
  have htop : (⊤ : Subgroup J) = CFSG.Quasithin.KGJ4.M4 ⊔ J4M2.B0grp.map φ := by
    rw [← hB]
    exact (sup_perfectCore_eq_top_of_sylow hS hzF hz1 hzS).symm
  have key : ∀ P : Subgroup J, P = J4M2.B0grp.map φ →
      IsHat (↥P ⧸ CFSG.pCore 2 ↥P) (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
        (⊤ : Subgroup J) = CFSG.Quasithin.KGJ4.M4 ⊔ P := by
    rintro P rfl
    exact ⟨hhat, htop⟩
  exact key _ hB

theorem modelL52_J_gen
    (hTL : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) :
    ModelL52 J (fun _ => True) := by
  intro Y V S z _ hYq hV hV1 hS hzV hz1 hzS
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have hcY : Nat.card ↥Y = Nat.card ↥(CFSG.pCore 2 ↥Y) * 9999360 := by
    rw [card_eq_card_pCore_mul, hYq]
  have hd : 2 ^ 10 * 31 ∣ Nat.card ↥Y := by
    rw [hcY]
    exact Dvd.dvd.mul_left (by norm_num) _
  have hPV : V ≤ pCoreOf 2 Y := hV.trans inf_le_left
  have hP1 : pCoreOf 2 Y ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hPV))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := le_conj_M4_of_twoLocal hTL (pCoreOf 2 Y)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hP1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y) ((Dvd.intro_left _ rfl).trans hd)
  have hP := comap_le_of_le_map_conj hg
  obtain ⟨hhat, htop⟩ := genL52_of_mulEquiv modelL52_M4_gen
    (Subgroup.topEquiv.trans (MulAut.conj g⁻¹)) le_top hP hYq hV hV1 hS hzV hz1 hzS
  rw [top_inf_eq] at hhat htop
  exact ⟨hhat, htop⟩

end L52

open CFSG.Sporadic.J4 in
theorem kg443J4GenL52_holds_gen
    (hTL : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) : KG443J4GenL52 := by
  intro G _ _ K Y V S z hJ hYK _ hYq hV hV1 _ hS hzV hz1 hzS
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  obtain ⟨e₀⟩ := hJ
  exact genL52_of_mulEquiv (L52.modelL52_J_gen hTL) (e₀.trans (seedEquiv hF.mat)) hYK trivial
    (L52.card_of_lieModel_l52 hYq) hV hV1 hS hzV hz1 hzS

end CFSG.Quasithin.H13.Ch4.G443J4

end
