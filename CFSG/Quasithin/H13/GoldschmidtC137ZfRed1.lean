module

public import CFSG.Quasithin.H13.GoldschmidtC137Inner
public import CFSG.Quasithin.Background.C124AsmEntry
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf
public import CFSG.Quasithin.Background.C124AsmNormal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem zf_equiv_alt6 {L V : Subgroup G} [IsMulCommutative ↥V] {Z : Subgroup ↥V}
    (hLN : L ≤ normalizer (V : Set G)) (hVL : ⁅V, L⁆ ≠ ⊥)
    (h : AlternatingNatural (V := ↥V) (autOn L V) ⊤ Z 6) :
    Nonempty (↥(alternatingGroup (Fin 6)) ≃* ↥(autOn L V)) := by
  obtain ⟨π, hsurj⟩ : ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥(autOn L V),
      Function.Surjective π := by
    obtain ⟨π, hs, -⟩ := h
    exact ⟨π, hs⟩
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases hsimp.eq_bot_or_eq_top_of_normal π.ker with hk | hk
  · exact ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hk, hsurj⟩⟩
  · exfalso
    apply hVL
    have hLC : L ≤ centralizer (V : Set G) := by
      intro l hl
      have h1 : conjAct V ⟨l, hLN hl⟩ ∈ autOn L V :=
        ⟨⟨l, hLN hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
      obtain ⟨a, ha⟩ := hsurj ⟨_, h1⟩
      have ha1 : π a = 1 := by
        rw [← MonoidHom.mem_ker, hk]
        exact Subgroup.mem_top a
      have h2 := congrArg Subtype.val ha
      rw [ha1] at h2
      exact (conjAct_eq_one_iff_gc V _).1 h2.symm
    rw [← Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hLC

theorem zf_isSimple_of_equiv_alt6 {Q : Type} [Group Q] (e : ↥(alternatingGroup (Fin 6)) ≃* Q) :
    IsSimpleGroup Q :=
  (MulEquiv.isSimpleGroup_congr e).mp (alternatingGroup.isSimpleGroup (by simp))

theorem zf_center_eq_bot_of_equiv_alt6 {Q : Type} [Group Q]
    (e : ↥(alternatingGroup (Fin 6)) ≃* Q) : Subgroup.center Q = ⊥ := by
  have hs := zf_isSimple_of_equiv_alt6 e
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative Q := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center Q := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.1 ha) b).symm⟩⟩
    have hnp : ¬ (Nat.card Q).Prime := by
      rw [← Nat.card_congr e.toEquiv, card_alt6]
      norm_num
    letI : CommGroup Q := { (inferInstance : Group Q) with
      mul_comm := fun a b => hc.is_comm.comm a b }
    exact hnp IsSimpleGroup.prime_card

theorem zf_exists_rho {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLN : L ≤ normalizer (V : Set G)) :
    ∃ ρ : ↥L →* ↥(autI hV L), Function.Surjective ρ ∧
      ∀ l : ↥L, ((ρ l : ↥(autI hV L)) : MulAut (IntMod V hV)) = convI hV ⟨l, hLN l.2⟩ := by
  refine ⟨(convHom hV L hLN).codRestrict (autI hV L) fun l => ?_, ?_, fun l => rfl⟩
  · rw [← range_convHom hV L hLN]
    exact ⟨l, rfl⟩
  · rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

theorem zf_inf_centralizer_le {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLN : L ≤ normalizer (V : Set G)) (hperf : ⁅L, L⁆ = L) (hVL : ⁅V, L⁆ ≠ ⊥)
    (hs : IsSimpleGroup ↥(autI hV L)) :
    L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ centralizer (V : Set G) := by
  obtain ⟨ρ, hρs, hρ⟩ := zf_exists_rho hV hLN
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hLU : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hLN hg) (Subgroup.le_normalizer hg)
  have hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ :=
    SBd5.commutator_commutator_eq_self hperf hLN
      (fun x hx y hy => B2F.isElemAbelian_comm hV hx hy)
  have hker : ∀ l : ↥L, ρ l = 1 ↔ (l : G) ∈ centralizer (V : Set G) := fun l => by
    rw [← OneMemClass.coe_eq_one, hρ, convI_eq_one_iff]
  set D' : Subgroup ↥L :=
    (L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).subgroupOf L with hD'
  have hD'n : D'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hD', Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), ?_⟩
    exact C124.conj_mem_centralizer_of_le hLU g.2 hn.2
  have hN1 : (D'.map ρ).Normal := Subgroup.Normal.map hD'n ρ hρs
  rcases hs.eq_bot_or_eq_top_of_normal (D'.map ρ) with h1 | h1
  · intro k hk
    have h2 : ρ ⟨k, hk.1⟩ ∈ D'.map ρ := ⟨⟨k, hk.1⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
    rw [h1, Subgroup.mem_bot] at h2
    exact (hker _).1 h2
  · exfalso
    have hLC : L ≤ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
      intro l hl
      have hmem : ρ ⟨l, hl⟩ ∈ D'.map ρ := by
        rw [h1]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdl⟩ := hmem
      have h3 : ρ (d⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hdl, inv_mul_cancel]
      have h4 := (hker _).1 h3
      have h5 : (d : G) ∈ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
        (Subgroup.mem_subgroupOf.1 hd).2
      have h6 : l = (d : G) * ((d⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
      rw [h6]
      exact Subgroup.mul_mem _ h5 (Subgroup.centralizer_le hUV h4)
    apply hVL
    rw [← hUU, ← Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hLC

variable [Finite G]

theorem zf_centralizer_U_le {X L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ normalizer (V : Set G)) (hLX : L ≤ X) (hn : X ≤ normalizer (L : Set G))
    (hfs : quasithinGenFitting (autI hV X) = autI hV L)
    (hCUV : L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ centralizer (V : Set G))
    (hZ : Subgroup.center ↥(autI hV L) = ⊥) :
    X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ centralizer (V : Set G) := by
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hXN hg) (hn hg)
  have hLU : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hLX.trans hXU
  intro x hx
  have hxX : x ∈ X := hx.1
  have hxN : x ∈ normalizer (V : Set G) := hXN hxX
  have hxc : ∀ u ∈ (⁅V, L⁆ : Subgroup G), x * u * x⁻¹ = u := fun u hu => by
    have := Subgroup.mem_centralizer_iff.1 hx.2 u hu
    rw [← this]
    group
  have hycomm : ∀ φ ∈ autI hV L, convI hV ⟨x, hxN⟩ * φ = φ * convI hV ⟨x, hxN⟩ := by
    intro φ hφ
    obtain ⟨l, hl, rfl⟩ := (mem_autI hV).1 hφ
    have hlU' : ∀ u ∈ (⁅V, L⁆ : Subgroup G), (l : G)⁻¹ * u * (l : G) ∈ (⁅V, L⁆ : Subgroup G) :=
      fun u hu => by
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer ((⁅V, L⁆ : Subgroup G) : Set G)).inv_mem
          (hLU hl)) u).1 hu
        simpa using this
    have hzL : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ L := by
      have h1 : x * (l : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hn hxX) l).1 hl
      exact L.mul_mem h1 (L.inv_mem hl)
    have hzU : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu₁ := hlU' u hu
      have h2 : x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x = (l : G)⁻¹ * u * (l : G) := by
        have := hxc _ hu₁
        calc x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x
            = x⁻¹ * (x * ((l : G)⁻¹ * u * (l : G)) * x⁻¹) * x := by rw [this]
          _ = (l : G)⁻¹ * u * (l : G) := by group
      have key : (x * (l : G) * x⁻¹ * (l : G)⁻¹) * u * (x * (l : G) * x⁻¹ * (l : G)⁻¹)⁻¹ = u := by
        have e1 : (x * (l : G) * x⁻¹ * (l : G)⁻¹) * u * (x * (l : G) * x⁻¹ * (l : G)⁻¹)⁻¹ =
            x * (l : G) * (x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x) * (l : G)⁻¹ * x⁻¹ := by group
        rw [e1, h2]
        have e2 : x * (l : G) * ((l : G)⁻¹ * u * (l : G)) * (l : G)⁻¹ * x⁻¹ = x * u * x⁻¹ := by
          group
        rw [e2, hxc u hu]
      exact (mul_inv_eq_iff_eq_mul.1 key).symm
    have hzV : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ centralizer (V : Set G) := hCUV ⟨hzL, hzU⟩
    have hzN : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ normalizer (V : Set G) :=
      (normalizer (V : Set G)).mul_mem
        ((normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hxN l.2)
          ((normalizer (V : Set G)).inv_mem hxN)) ((normalizer (V : Set G)).inv_mem l.2)
    have h1 := (convI_eq_one_iff hV ⟨_, hzN⟩).2 hzV
    have h2 : (⟨x * (l : G) * x⁻¹ * (l : G)⁻¹, hzN⟩ : ↥(normalizer (V : Set G))) =
        ⟨x, hxN⟩ * l * ⟨x, hxN⟩⁻¹ * l⁻¹ := Subtype.ext rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hyX : convI hV ⟨x, hxN⟩ ∈ autI hV X := convI_mem_autI hV hxX hxN
  have hycent : convI hV ⟨x, hxN⟩ ∈ centralizer
      ((quasithinGenFitting (autI hV X) : Subgroup (MulAut (IntMod V hV))) : Set _) := by
    rw [hfs, Subgroup.mem_centralizer_iff]
    intro φ hφ
    exact (hycomm φ hφ).symm
  have hyL : convI hV ⟨x, hxN⟩ ∈ autI hV L := by
    rw [← hfs]
    exact centralizer_quasithinGenFitting_le (autI hV X) ⟨hyX, hycent⟩
  have hcenter : (⟨convI hV ⟨x, hxN⟩, hyL⟩ : ↥(autI hV L)) ∈ Subgroup.center ↥(autI hV L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hycomm g g.2).symm
  rw [hZ, Subgroup.mem_bot] at hcenter
  have h1 : convI hV ⟨x, hxN⟩ = 1 := congrArg Subtype.val hcenter
  exact (convI_eq_one_iff hV ⟨x, hxN⟩).1 h1

theorem zf_reduce {X T V L : Subgroup G} (hred : IsTwoReducedIn X V) (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hcomp : L ∈ cComp X)
    (htype : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L)
    (hVL : ⁅V, L⁆ ≠ ⊥)
    (hnat : ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤
      ((centralizer (L : Set G)).subgroupOf V) 6) :
    IsTwoReducedIn X ⁅V, L⁆ ∧ ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ ∧
      X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G) := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  have hLX : L ≤ X := le_of_mem_cComp hcomp
  have hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hcomp
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hXN
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hUe : IsElemAbelian 2 ⁅V, L⁆ := B2F.isElemAbelian_mono hUV hV
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hXN hg) (hn hg)
  have hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ :=
    SBd5.commutator_commutator_eq_self hperf hLN
      (fun x hx y hy => B2F.isElemAbelian_comm hV hx hy)
  have halt : IsAltQuotient L (oTwoZIn L) 6 :=
    htype.elim isAltQuotient_of_a6 isAltQuotient_of_hatA6
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    C124.isQuasisimple_of_altQuotient hcomp halt (by norm_num)
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  obtain ⟨-, -, hfs, -⟩ := C124.B2_10_2 hV hred hQT le_rfl hT hLX hn hprod hVL (Or.inl hLq)
  obtain ⟨hc, hnat'⟩ := hnat
  obtain ⟨e⟩ := zf_equiv_alt6 hLN hVL hnat'
  have e' : ↥(alternatingGroup (Fin 6)) ≃* ↥(autI hV L) := e
  have hCUV := zf_inf_centralizer_le hV hLN hperf hVL (zf_isSimple_of_equiv_alt6 e')
  have hle := zf_centralizer_U_le hV hXN hLX hn hfs hCUV (zf_center_eq_bot_of_equiv_alt6 e')
  have hCeq : X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G) :=
    le_antisymm (le_inf inf_le_left hle) (inf_le_inf_left X (Subgroup.centralizer_le hUV))
  refine ⟨⟨hUV.trans hred.1, hXU, hUe, fun D hDX hXD hD => ?_⟩, hUU, hCeq⟩
  have hD' : D ≤ centralizer (V : Set G) := by
    refine hred.2.2.2 D hDX hXD fun d hd => ?_
    obtain ⟨k, hk⟩ := hD d hd
    exact ⟨k, hle ⟨(pow_mem (hDX hd) _ : d ^ 2 ^ k ∈ X), hk⟩⟩
  exact hD'.trans (Subgroup.centralizer_le hUV)

theorem zf_autOn_le_of_centralizer_eq {X A B V U : Subgroup G}
    (hVN : X ≤ normalizer (V : Set G)) (hUN : X ≤ normalizer (U : Set G))
    (hAX : A ≤ X) (hBX : B ≤ X)
    (hCeq : X ⊓ centralizer (U : Set G) = X ⊓ centralizer (V : Set G))
    (h : autOn A U ≤ autOn B U) : autOn A V ≤ autOn B V := by
  rintro φ ⟨⟨a, haN⟩, ha, rfl⟩
  have haA : a ∈ A := Subgroup.mem_subgroupOf.1 ha
  have h1 : conjAct U ⟨a, hUN (hAX haA)⟩ ∈ autOn A U :=
    ⟨⟨a, hUN (hAX haA)⟩, Subgroup.mem_subgroupOf.2 haA, rfl⟩
  obtain ⟨⟨b, hbN⟩, hb, hbeq⟩ := h h1
  have hbB : b ∈ B := Subgroup.mem_subgroupOf.1 hb
  have h2 : conjAct U ((⟨b, hbN⟩ : ↥(normalizer (U : Set G)))⁻¹ * ⟨a, hUN (hAX haA)⟩) = 1 := by
    rw [map_mul, map_inv, hbeq, inv_mul_cancel]
  have h3 : b⁻¹ * a ∈ centralizer (U : Set G) := (conjAct_eq_one_iff_gc U _).1 h2
  have h4 : b⁻¹ * a ∈ centralizer (V : Set G) := by
    have h5 : b⁻¹ * a ∈ X ⊓ centralizer (U : Set G) :=
      ⟨X.mul_mem (X.inv_mem (hBX hbB)) (hAX haA), h3⟩
    rw [hCeq] at h5
    exact h5.2
  have hbV : b ∈ normalizer (V : Set G) := hVN (hBX hbB)
  have h6 : conjAct V ((⟨b, hbV⟩ : ↥(normalizer (V : Set G)))⁻¹ * ⟨a, haN⟩) = 1 :=
    (conjAct_eq_one_iff_gc V _).2 h4
  rw [map_mul, map_inv, inv_mul_eq_one] at h6
  exact ⟨⟨b, hbV⟩, Subgroup.mem_subgroupOf.2 hbB, h6⟩

theorem zf_not_autOn_le_of_centralizer_eq {X A B V U : Subgroup G}
    (hVN : X ≤ normalizer (V : Set G)) (hUN : X ≤ normalizer (U : Set G))
    (hAX : A ≤ X) (hBX : B ≤ X)
    (hCeq : X ⊓ centralizer (U : Set G) = X ⊓ centralizer (V : Set G))
    (h : ¬ autOn A V ≤ autOn B V) : ¬ autOn A U ≤ autOn B U :=
  fun h' => h (zf_autOn_le_of_centralizer_eq hVN hUN hAX hBX hCeq h')

end CFSG.Quasithin.H13.U3.GC137
