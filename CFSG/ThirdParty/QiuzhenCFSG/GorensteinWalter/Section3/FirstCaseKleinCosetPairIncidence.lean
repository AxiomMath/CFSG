module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCommutingPairs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The aggregate commuting-pair fiber over `s ∈ Ĥ ∖ V` is equivalent to
commuting off-diagonal pairs in the corresponding non-base involution coset.
The product of a pair of external involutions is forced outside `V` by the
ambient centralizer bound for nontrivial elements of `V`. -/
public theorem firstCase_klein_commuting_pair_coset_incidence
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nonempty (
      (Sigma fun s : {s : G // IsInvolution s ∧ s ∈ c.Hhat ∧
          s ∉ twoCoreOf c.Hhat} =>
        {z : G // IsInvolution z ∧ z ∉ c.Hhat ∧ Commute (s : G) z}) ≃
      (let Ω := G ⧸ c.Hhat
       let π : {z : G // IsInvolution z ∧ z ∉ c.Hhat} → Ω :=
         fun z => cosetInvolution_proj c.Hhat z
       let base := cosetInvolution_base c.Hhat
       let Fiber := fun ω : Ω => {z : {z : G // IsInvolution z ∧ z ∉ c.Hhat} // π z = ω}
       let Nonbase := {ω : Ω // ω ≠ base}
       Σ ω : Nonbase,
         {p : Fiber ω.1 × Fiber ω.1 // p.1 ≠ p.2 ∧
           Commute (p.1.1 : G) (p.2.1 : G)})) := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  let S : Type u := {s : G // IsInvolution s ∧ s ∈ c.Hhat ∧ s ∉ V}
  let Q : S → Type u := fun s =>
    {z : G // IsInvolution z ∧ z ∉ c.Hhat ∧ Commute (s : G) z}
  let Ω := G ⧸ c.Hhat
  let InvOut : Type u := {z : G // IsInvolution z ∧ z ∉ c.Hhat}
  let π : InvOut → Ω := fun z => cosetInvolution_proj c.Hhat z
  let base : Ω := cosetInvolution_base c.Hhat
  let Fiber : Ω → Type u := fun ω => {z : InvOut // π z = ω}
  let Nonbase := {ω : Ω // ω ≠ base}
  let OffPair := Σ ω : Nonbase,
    {p : Fiber ω.1 × Fiber ω.1 // p.1 ≠ p.2 ∧
      Commute (p.1.1 : G) (p.2.1 : G)}
  have proj_eq (x : G) : cosetInvolution_proj c.Hhat x =
      QuotientGroup.mk (x⁻¹) := by rfl
  have base_eq : cosetInvolution_base c.Hhat =
      QuotientGroup.mk ((1 : G)⁻¹) := by rfl
  have invSelf {x : G} (hx : IsInvolution x) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx.2)
  have hbase_of_mem {z : InvOut} (hz : π z = base) :
      (z : G) ∈ c.Hhat := by
    change cosetInvolution_proj c.Hhat (z : G) =
      cosetInvolution_base c.Hhat at hz
    rw [proj_eq, base_eq] at hz
    rw [QuotientGroup.eq] at hz
    simpa [invSelf z.2.1] using hz
  have hprod_mem_H {y z : G}
      (hyI : IsInvolution y) (hzI : IsInvolution z)
      (hyz : Commute y z)
      (hcos : cosetInvolution_proj c.Hhat y = cosetInvolution_proj c.Hhat z) :
      y * z ∈ c.Hhat := by
    rw [proj_eq, proj_eq] at hcos
    have hq := (QuotientGroup.eq (s := c.Hhat)).mp hcos
    have hyInv := invSelf hyI
    have hzInv := invSelf hzI
    simpa [hyInv, hzInv, hyz.eq] using hq
  have hprod_notV {y z : G}
      (hyH : y ∉ c.Hhat) (hzH : z ∉ c.Hhat)
      (hyI : IsInvolution y) (hzI : IsInvolution z)
      (hyz : Commute y z) (hyne : y ≠ z)
      (hprodH : y * z ∈ c.Hhat) :
      y * z ∉ V := by
    intro hV
    have hprodne : y * z ≠ 1 := by
      intro h
      apply hyne
      calc
        y = (y * z) * z⁻¹ := by group
        _ = z := by rw [h, invSelf hzI]; simp
    have hycent : y ∈ Subgroup.centralizer ({y * z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        y * (y * z) = y * (z * y) := by rw [hyz.eq]
        _ = (y * z) * y := by group
    have hle := firstCase_klein_centralizer_twoCore_le_Hhat hmin c hklein
      (y * z) hV hprodne
    exact hyH (hle hycent)
  have hmap :
      Sigma Q ≃ OffPair := by
    let toFun : Sigma Q → OffPair := fun p => by
      let s : S := p.1
      let z : Q s := p.2
      have hyI : IsInvolution ((s : G) * (z : G)) := by
        refine ⟨?_, ?_⟩
        · intro h
          apply z.2.2.1
          rw [eq_inv_of_mul_eq_one_right h]
          exact c.Hhat.inv_mem s.2.2.1
        · rw [pow_two]
          calc
            ((s : G) * (z : G)) * ((s : G) * (z : G)) =
                (s : G) * ((z : G) * (s : G)) * (z : G) := by group
            _ = (s : G) * ((s : G) * (z : G)) * (z : G) := by rw [z.2.2.2.eq]
            _ = ((s : G) * (s : G)) * ((z : G) * (z : G)) := by group
            _ = 1 := by rw [← pow_two, s.2.1.2, ← pow_two, z.2.1.2]; simp
      have hyH : (s : G) * (z : G) ∉ c.Hhat := by
        intro h
        apply z.2.2.1
        simpa [mul_assoc] using c.Hhat.mul_mem (c.Hhat.inv_mem s.2.2.1) h
      let zOut : InvOut := ⟨(z : G), z.2.1, z.2.2.1⟩
      let y : InvOut := ⟨(s : G) * (z : G), hyI, hyH⟩
      have hbase : π zOut ≠ base := by
        intro hzbase
        exact z.2.2.1 (hbase_of_mem hzbase)
      let ω : Nonbase := ⟨π zOut, hbase⟩
      have hycos : π y = π zOut := by
        dsimp [y, zOut, π]
        rw [proj_eq, proj_eq]
        apply (QuotientGroup.eq (s := c.Hhat)).mpr
        have heq : (((s : G) * (z : G))⁻¹)⁻¹ * (z : G)⁻¹ =
            (s : G) := by
          calc
            (((s : G) * (z : G))⁻¹)⁻¹ * (z : G)⁻¹ =
                ((s : G) * (z : G)) * (z : G)⁻¹ := by rw [inv_inv]
            _ = (s : G) := by
              rw [invSelf z.2.1]
              rw [mul_assoc, ← pow_two, z.2.1.2]
              simp
        rw [heq]
        exact s.2.2.1
      have hne : zOut ≠ y := by
        intro h
        have hv : (z : G) = (s : G) * (z : G) := congrArg Subtype.val h
        apply s.2.1.1
        calc
          (s : G) = ((s : G) * (z : G)) * (z : G)⁻¹ := by group
          _ = (z : G) * (z : G)⁻¹ := by rw [← hv]
          _ = 1 := by simp
      have hcomm : Commute (z : G) ((y : InvOut) : G) := by
        exact z.2.2.2.symm.mul_right (Commute.refl (z : G))
      let zFib : Fiber ω.1 := ⟨zOut, rfl⟩
      let yFib : Fiber ω.1 := ⟨y, hycos⟩
      have hneFib : zFib ≠ yFib := by
        intro h
        apply hne
        exact congrArg Subtype.val h
      exact ⟨ω, ⟨(zFib, yFib), hneFib, hcomm⟩⟩
    let invFun : OffPair → Sigma Q := fun p => by
      let z : InvOut := p.2.1.1
      let y : InvOut := p.2.1.2
      let s0 : G := (y : G) * (z : G)
      have hyz : Commute (y : G) (z : G) := by
        simpa [y, z] using p.2.2.2.symm
      have hcos : cosetInvolution_proj c.Hhat (y : G) =
          cosetInvolution_proj c.Hhat (z : G) := by
        simpa [π] using p.2.1.2.2.trans p.2.1.1.2.symm
      have hsH : s0 ∈ c.Hhat := hprod_mem_H y.2.1 z.2.1 hyz hcos
      have hneG : (y : G) ≠ (z : G) := by
        intro h
        apply p.2.2.1
        apply Subtype.ext
        apply Subtype.ext
        simpa [y, z] using h.symm
      have hsI : IsInvolution s0 := by
        refine ⟨?_, ?_⟩
        · intro h
          change ((y : G) * (z : G)) = 1 at h
          apply hneG
          calc
            (y : G) = ((y : G) * (z : G)) * (z : G)⁻¹ := by group
            _ = (1 : G) * (z : G)⁻¹ := by rw [h]
            _ = (z : G) := by rw [invSelf z.2.1]; simp
        · rw [pow_two]
          calc
            ((y : G) * (z : G)) * ((y : G) * (z : G)) =
                (y : G) * ((z : G) * (y : G)) * (z : G) := by group
            _ = (y : G) * ((y : G) * (z : G)) * (z : G) := by rw [← hyz.eq]
            _ = ((y : G) * (y : G)) * ((z : G) * (z : G)) := by group
            _ = 1 := by rw [← pow_two, y.2.1.2, ← pow_two, z.2.1.2]; simp
      have hsV : s0 ∉ V := hprod_notV y.2.2 z.2.2 y.2.1 z.2.1
        hyz hneG hsH
      let s : S := ⟨s0, hsI, hsH, hsV⟩
      have hsz : Commute s0 (z : G) := by
        calc
          s0 * (z : G) = ((y : G) * (z : G)) * (z : G) := by rfl
          _ = ((z : G) * (y : G)) * (z : G) := by rw [hyz.eq]
          _ = (z : G) * s0 := by dsimp [s0]; group
      exact ⟨s, ⟨(z : G), z.2.1, z.2.2, hsz⟩⟩
    let e : Sigma Q ≃ OffPair :=
      { toFun := toFun
        invFun := invFun
        left_inv := by
          rintro ⟨s, z⟩
          have hsVal : ((invFun (toFun ⟨s, z⟩)).1 : G) = (s : G) := by
            dsimp [invFun, toFun]
            have hzMul : (z : G) * (z : G) = 1 := by
              simpa [pow_two] using z.2.1.2
            calc
              ((s : G) * (z : G)) * (z : G) =
                  (s : G) * ((z : G) * (z : G)) := by group
              _ = (s : G) := by rw [hzMul]; simp
          have hsEq : (invFun (toFun ⟨s, z⟩)).1 = s :=
            Subtype.ext hsVal
          apply Sigma.ext hsEq
          apply (Subtype.heq_iff_coe_eq (fun a : G => by
            change
              (IsInvolution a ∧ a ∉ c.Hhat ∧
                Commute ((invFun (toFun ⟨s, z⟩)).1 : G) a) ↔
              (IsInvolution a ∧ a ∉ c.Hhat ∧ Commute (s : G) a)
            rw [hsEq])).2
          rfl
        right_inv := by
          rintro ⟨ω, pp⟩
          have hω0 : (toFun (invFun ⟨ω, pp⟩)).1 = ω := by
            apply Subtype.ext
            dsimp [toFun, invFun]
            exact pp.1.1.2
          generalize hqdef : toFun (invFun ⟨ω, pp⟩) = q
          have hω' : q.1 = ω := by
            simpa [hqdef] using hω0
          cases q with
          | mk ωq qq =>
            have hω : ωq = ω := by
              apply Subtype.ext
              exact congrArg Subtype.val hω'
            cases hω
            apply congrArg (fun r => Sigma.mk ω r)
            apply Subtype.ext
            apply Prod.ext
            · apply Subtype.ext
              apply Subtype.ext
              have hfirst := congrArg
                (fun r : OffPair => ((r.2.1.1 : Fiber r.1) : G)) hqdef
              dsimp [toFun, invFun] at hfirst
              simpa using hfirst.symm
            · apply Subtype.ext
              apply Subtype.ext
              have hzMul : (pp.1.1.1 : G) * (pp.1.1.1 : G) = 1 := by
                simpa [pow_two] using pp.1.1.1.2.1.2
              have hsecond := congrArg
                (fun r : OffPair => ((r.2.1.2 : Fiber r.1) : G)) hqdef
              dsimp [toFun, invFun] at hsecond
              calc
                (qq.1.2 : G) =
                    ((pp.1.2.1 : G) * (pp.1.1.1 : G)) *
                      (pp.1.1.1 : G) := by simpa using hsecond.symm
                _ =
                    (pp.1.2.1 : G) *
                      ((pp.1.1.1 : G) * (pp.1.1.1 : G)) := by group
                _ = (pp.1.2.1 : G) := by rw [hzMul]; simp }
    exact e
  exact ⟨by simpa [S, Q, Ω, π, base, Fiber, Nonbase, OffPair] using hmap⟩

end CFSG.GorensteinWalter
