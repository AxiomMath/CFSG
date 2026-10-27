module

public import CFSG.Quasithin.EmptyFaithful.S146zWG

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.C2Push CFSG.Quasithin.S146zV CFSG.Quasithin.SBc17
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace WreathData

variable {H R J J' : Subgroup G} {ρ : G} (d : WreathData H R J J' ρ)

include d

theorem card_center_quot_le_wAut :
    Nat.card ((↥J ⧸ CFSG.pCore 2 ↥J) ⧸ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) ≤
      Nat.card ↥(wAut J J' R J) := by
  obtain ⟨hq₁, -, -, -, -, -, -⟩ := d.moduleFacts
  obtain ⟨f, hf⟩ := exists_surj_wAut (J := J) (J' := J') (R := R) J (J_le_wY J J' R)
  set Jb := ↥J ⧸ CFSG.pCore 2 ↥J with hJb
  let mk : ↥J →* Jb := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hmk : Function.Surjective mk := QuotientGroup.mk'_surjective _
  let g : ↥J →* Jb ⧸ Subgroup.center Jb := (QuotientGroup.mk' (Subgroup.center Jb)).comp mk
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hmk
  have hker : f.ker ≤ g.ker := by
    have hnormal : (f.ker.map mk).Normal := Subgroup.Normal.map inferInstance mk hmk
    by_cases htop : f.ker.map mk = ⊤
    · exfalso
      have hP : IsPGroup 2 ↥(wAut J J' R J) := by
        intro φ
        obtain ⟨j, rfl⟩ := hf φ
        have hj : mk j ∈ f.ker.map mk := by rw [htop]; trivial
        obtain ⟨n, hn, hnj⟩ := Subgroup.mem_map.mp hj
        have hjn : n⁻¹ * j ∈ CFSG.pCore 2 ↥J := by
          rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥J)]
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          rw [show (mk n) = QuotientGroup.mk' (CFSG.pCore 2 ↥J) n from rfl] at hnj
          have : mk n = mk j := hnj
          rw [this, inv_mul_cancel]
        obtain ⟨e, he⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥J) ⟨_, hjn⟩
        have hfn : f n = 1 := hn
        have hfk : f j = f (n⁻¹ * j) := by rw [map_mul, map_inv, hfn, inv_one, one_mul]
        refine ⟨e, ?_⟩
        rw [hfk, ← map_pow]
        have : (n⁻¹ * j) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
        rw [this, map_one]
      have hsolv : Group.IsSolvable ↥(wAut J J' R J) := by
        have := hP.isNilpotent
        infer_instance
      have : Nontrivial ↥(wAut J J' R J) := CFSG.LocalCores.isQuasisimple_nontrivial hq₁
      have : Group.IsPerfect ↥(wAut J J' R J) := hq₁.1
      exact Group.IsPerfect.not_isSolvable _ hsolv
    · have hq := B1Red.isQuasisimple_to_open d.cfg.quasi
      have hc := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq
        (f.ker.map mk) htop
      intro x hx
      have := hc (Subgroup.mem_map_of_mem mk hx)
      exact (QuotientGroup.eq_one_iff _).mpr this
  let g' : (↥J ⧸ f.ker) →* Jb ⧸ Subgroup.center Jb := QuotientGroup.lift f.ker g hker
  have hg' : Function.Surjective g' := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨QuotientGroup.mk x, rfl⟩
  calc Nat.card (Jb ⧸ Subgroup.center Jb) ≤ Nat.card (↥J ⧸ f.ker) :=
        Nat.card_le_card_of_surjective g' hg'
    _ = Nat.card ↥(wAut J J' R J) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv

end WreathData

end CFSG.Quasithin.S146zW
