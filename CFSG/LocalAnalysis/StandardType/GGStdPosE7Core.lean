module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
import CFSG.LocalAnalysis.StandardType.GGStdPosIsogCore
import CFSG.LocalAnalysis.StandardType.GGStdPosE8Core
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
import CFSG.LieType.Steinberg.Isogeny.E7
import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

namespace StdPosExc

private theorem e7Isogeny_mem_rootGroup_iff
    {F : Type} [Field F] [Finite F] [CharP F 2] {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) (y : ↥(e7Data_valid.minGroup F)) :
    e7Isogeny F y ∈ rootGroup (rootOperatorFamily .E7) F γ ↔ y ∈ (e7Datum F).rootGroup γ := by
  have hε : ((e7Eps γ : ℤ) : F) * (e7Eps γ : F) = 1 := by
    rcases e7Eps_eq_one_or γ with h | h <;> simp [h]
  constructor
  · intro hy
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff hγ _).1 hy
    refine (e7Data_valid.mem_rootGroup F).2 ⟨(e7Eps γ : F) * c, ?_⟩
    apply SeitzReduction.E8Pilot.e7Isogeny_injective_of_charTwo
    rw [e7Isogeny_xm, ← mul_assoc, hε, one_mul, hc]
  · intro hy
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup F).1 hy
    rw [e7Isogeny_xm]
    exact xPar_mem hγ _

private theorem mem_ggTorus_e7Datum
    {F : Type} [Field F] [Finite F] [CharP F 2] {h : ↥(e7Data_valid.minGroup F)}
    (hh : ((e7Isogeny F h : adjointGroup .E7 F) : ModGL .E7 F) ∈ torusGroup .E7 F) :
    h ∈ ggTorus (e7Datum F) := by
  have h1 := mem_ggTorus_adjDatum (F := rootOperatorFamily .E7) hh
  simp only [ggTorus, Subgroup.mem_iInf] at h1 ⊢
  intro γ hγ
  have hγ' : IsRoot .E7 γ := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 F).1 hγ
  have h2 := h1 γ (mem_adjDatum_roots.2 hγ')
  rw [Subgroup.mem_normalizer_iff] at h2 ⊢
  intro z
  rw [← e7Isogeny_mem_rootGroup_iff hγ', ← e7Isogeny_mem_rootGroup_iff hγ', map_mul, map_mul,
    map_inv]
  exact h2 _

theorem exists_stdPos_e7
    {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G] [Finite G]
    {ψ : ↥(e7Data_valid.minGroup F) →* G} {p : ℕ} {Bs : Subgroup G}
    (hker : ψ.ker ≤ Subgroup.center ↥(e7Data_valid.minGroup F)) (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, GGPsiInnerDiag (e7Datum F) ψ b)
    (hc : p ^ 7 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs)
    (hT : GGExcToralRankInput .E7 F p) :
    ∃ s : ↥(e7Data_valid.minGroup F),
      GGKGPosStdPos (e7Datum F) (ψ.comp (MulAut.conj s).toMonoidHom) Bs := by
  have hinj : Function.Injective (e7Isogeny F) :=
    SeitzReduction.E8Pilot.e7Isogeny_injective_of_charTwo
  refine exists_stdPos_of_toral (V := (TableBExc.torusPow .E7 F p).comap (e7Isogeny F)) (r := 7)
    SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot hker
    (fun _ hv => mem_ggTorus_e7Datum (TableBExc.mem_torusPow.1 (Subgroup.mem_comap.1 hv)).1)
    (fun E hE hE7 => ?_) hBs
    (fun b hb => PsiDiag.Minu.exists_mem_centralizer_E7 ψ hker (hinn b hb)) hc
  have hEι : IsElemAbelian p (E.map (e7Isogeny F)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      apply Subtype.ext
      change e7Isogeny F x * e7Isogeny F y = e7Isogeny F y * e7Isogeny F x
      rw [← map_mul, ← map_mul]
      exact congrArg (e7Isogeny F) (congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  obtain ⟨g, hg⟩ := hT _ hEι (by rw [Subgroup.card_map_of_injective hinj]; exact hE7)
  obtain ⟨g', rfl⟩ := e7Isogeny_surjective F g
  refine ⟨g', ?_⟩
  rintro _ ⟨e, he, rfl⟩
  rw [Subgroup.mem_comap, ← hg]
  refine ⟨e7Isogeny F e, ⟨e, he, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

end StdPosExc

end CFSG.StandardType

end
