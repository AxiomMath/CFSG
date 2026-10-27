module

public import CFSG.Quasithin.Vol2.Ch12Sec6L14b
public import CFSG.Quasithin.Vol2.KGFactM22Hex
public import CFSG.Quasithin.Vol2.Ch12Sec6L12a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

theorem eq_bot_of_normal_A6 {N : Subgroup ↥(alternatingGroup (Fin 6))} (hN : N.Normal)
    (h2 : IsPGroup 2 ↥N) : N = ⊥ := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := h2 ⟨S126M22.a6a, h ▸ Subgroup.mem_top _⟩
    have hk' : S126M22.a6a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 := orderOf_dvd_of_pow_eq_one hk'
    rw [orderOf_eq_prime S126M22.a6a_pow S126M22.a6a_ne] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem o2Iso_autOn_Lv (h1222 : Stmt12_2_2) (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    quasithinO2QuotientIso (autOn (Lv L v) (Usec Kv S)) ↥(alternatingGroup (Fin 6)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  have hLvU : Lv L v ≤ Subgroup.normalizer (Usec Kv S : Set G) :=
    hC.lv_le.trans (Kv_le_normalizer_Usec hC)
  set g := InternalSec.autOnHom hLvU with hgdef
  have hgs : Function.Surjective g := InternalSec.autOnHom_surjective hLvU
  obtain ⟨hψs, hψk⟩ := o2Iso_Lv h1222 F hH hv hβ
  set ψ := psiLv h1222 F hH hv hβ with hψdef
  have hle : g.ker ≤ ψ.ker := by
    intro l hl
    rw [InternalSec.mem_ker_autOnHom] at hl
    have hlO : (l : G) ∈ pCoreOf 2 (Kv ⊔ S) := by
      rw [hO]
      exact ⟨(le_sup_left : Kv ≤ Kv ⊔ S) (hC.lv_le l.2), hl⟩
    have hLO : Lv L v ⊓ pCoreOf 2 (Kv ⊔ S) ≤ pCoreOf 2 (Lv L v) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun x hx => A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
          (le_normalizer_pCoreOf 2 (Kv ⊔ S)
            ((le_sup_left : Kv ≤ Kv ⊔ S) (hC.lv_le hx))))
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    obtain ⟨y, hy, hyl⟩ := hLO ⟨l.2, hlO⟩
    rw [hψk, show l = y from (Subtype.ext hyl).symm]
    exact hy
  set e := QuotientGroup.quotientKerEquivOfSurjective g hgs with hedef
  let ψb : ↥(autOn (Lv L v) (Usec Kv S)) →* ↥(alternatingGroup (Fin 6)) :=
    (QuotientGroup.lift g.ker ψ hle).comp e.symm.toMonoidHom
  have hψb : ∀ l, ψb (g l) = ψ l := by
    intro l
    have h1 : e.symm (g l) = QuotientGroup.mk l := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ψb, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  refine ⟨ψb, fun a => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := hψs a
    exact ⟨g l, hψb l⟩
  · ext b
    rw [MonoidHom.mem_ker]
    obtain ⟨l, rfl⟩ := hgs b
    constructor
    · intro hb
      rw [hψb, ← MonoidHom.mem_ker, hψk] at hb
      have hn : ((CFSG.Open.pCore 2 ↥(Lv L v)).map g).Normal :=
        Subgroup.Normal.map inferInstance g hgs
      have h2 : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥(Lv L v)).map g) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥(Lv L v))).map g
      exact CFSG.LieType.BorelTits.le_pCore 2 hn h2 ⟨l, hb, rfl⟩
    · intro hb
      have hn : ((CFSG.Open.pCore 2 ↥(autOn (Lv L v) (Usec Kv S))).map ψb).Normal :=
        Subgroup.Normal.map inferInstance ψb (fun a => by
          obtain ⟨l, rfl⟩ := hψs a
          exact ⟨g l, hψb l⟩)
      have h2 : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥(autOn (Lv L v) (Usec Kv S))).map ψb) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥(autOn (Lv L v) (Usec Kv S)))).map ψb
      have h3 := eq_bot_of_normal_A6 hn h2
      have h4 : ψb (g l) ∈ (CFSG.Open.pCore 2 ↥(autOn (Lv L v) (Usec Kv S))).map ψb :=
        ⟨_, hb, rfl⟩
      rw [h3, Subgroup.mem_bot] at h4
      exact h4

end S126T2

end CFSG.Quasithin.H13
