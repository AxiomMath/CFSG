module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatGen

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.ZTrans
  CFSG.Quasithin.H13
open scoped commutatorElement

@[expose] def MB4bc {V : Type} [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)) : Prop :=
  (∃ z ∈ perfectCore (H ⊓ stabSub (fixV X)), z ^ 3 = 1 ∧
      (∀ g ∈ perfectCore (H ⊓ stabSub (fixV X)),
        ⁅z, g⁆ ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X)))) ∧
      ∃ b ∈ s828BPrime H X, z b * b⁻¹ ∉ fixV X) ∧
    (∀ S : Subgroup (MulAut V), S ≤ H ⊓ stabSub (fixV X) → IsPGroup 2 ↥S →
      ¬ 2 ∣ (S.subgroupOf (H ⊓ stabSub (fixV X))).index →
        ∃ t ∈ S, t ^ 2 = 1 ∧ (∃ g ∈ H, g * t * g⁻¹ ∈ X) ∧
          ∀ z ∈ perfectCore (H ⊓ stabSub (fixV X)),
            (∀ g ∈ perfectCore (H ⊓ stabSub (fixV X)),
              ⁅z, g⁆ ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X)))) →
            t * z * t⁻¹ * z ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))))

section Transport

variable {V W : Type} [CommGroup V] [CommGroup W] [Finite V] [Finite W]

theorem mb4bc_of_map (e : V ≃* W) (H X : Subgroup (MulAut V))
    (h : MB4bc (H.map (congrHom e)) (X.map (congrHom e))) : MB4bc H X := by
  have hinj : Function.Injective (congrHom e) := congrHom_injective e
  have hN : (H ⊓ stabSub (fixV X)).map (congrHom e) =
      H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e))) := map_inf_stab_congrHom e H X
  have hP : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) =
      perfectCore (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e)))) :=
    perfectCore_inf_stab_map e H X
  have hO : (pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X)))).map (congrHom e) =
      pCoreOf 2 (perfectCore (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e))))) := by
    rw [← hP, pCoreOf_map_congrHom]
  have hmem : ∀ {K : Subgroup (MulAut V)} {x : MulAut V}, congrHom e x ∈ K.map (congrHom e) ↔
      x ∈ K := fun {K x} => Subgroup.mem_map_iff_mem hinj
  obtain ⟨⟨zs, hzs, hz3, hcent, bs, hbs, hbn⟩, hc⟩ := h
  refine ⟨?_, ?_⟩
  ·
    rw [← hP] at hzs
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hzs
    refine ⟨z, hz, ?_, ?_, ?_⟩
    · apply hinj
      rw [map_pow, hz3, map_one]
    · intro g hg
      have h1 := hcent (congrHom e g) (by rw [← hP]; exact Subgroup.mem_map_of_mem _ hg)
      have h2 : congrHom e ⁅z, g⁆ = ⁅congrHom e z, congrHom e g⁆ :=
        map_commutatorElement (congrHom e) z g
      rw [← h2, ← hO] at h1
      exact hmem.1 h1
    · rw [← s828BPrime_map] at hbs
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hbs
      refine ⟨b, hb, fun hzb => hbn ?_⟩
      have e1 : e (z b * b⁻¹) = congrHom e z (e b) * (e b)⁻¹ := by
        have hs : e.symm (e b) = b := e.symm_apply_apply b
        show e (z b * b⁻¹) = e (z (e.symm (e b))) * (e b)⁻¹
        rw [hs, map_mul, map_inv]
      show congrHom e z (e.toMonoidHom b) * (e.toMonoidHom b)⁻¹ ∈ fixV (X.map (congrHom e))
      rw [fixV_map_congrHom]
      exact ⟨_, hzb, by simpa using e1.symm⟩
  ·
    intro S hSN hSp hidx
    have hS' : S.map (congrHom e) ≤ H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e))) := by
      rw [← hN]; exact Subgroup.map_mono hSN
    have hSp' : IsPGroup 2 ↥(S.map (congrHom e)) := hSp.map _
    have hidx' : ¬ 2 ∣ ((S.map (congrHom e)).subgroupOf
        (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e))))).index := by
      have := Subgroup.relIndex_map_map_of_injective S (H ⊓ stabSub (fixV X)) hinj
      rw [hN] at this
      unfold Subgroup.relIndex at this
      rw [this]
      exact hidx
    obtain ⟨ts, hts, hts2, ⟨gs, hgs, hgx⟩, hinv⟩ := hc _ hS' hSp' hidx'
    obtain ⟨t, htS, rfl⟩ := Subgroup.mem_map.1 hts
    obtain ⟨g, hgH, rfl⟩ := Subgroup.mem_map.1 hgs
    refine ⟨t, htS, ?_, ⟨g, hgH, ?_⟩, ?_⟩
    · apply hinj
      rw [map_pow, hts2, map_one]
    · have : congrHom e (g * t * g⁻¹) = congrHom e g * congrHom e t * (congrHom e g)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [← this] at hgx
      exact hmem.1 hgx
    · intro z hz hzc
      have h1 := hinv (congrHom e z) (by rw [← hP]; exact Subgroup.mem_map_of_mem _ hz)
        (fun g' hg' => by
          rw [← hP] at hg'
          obtain ⟨g'', hg'', rfl⟩ := Subgroup.mem_map.1 hg'
          have h2 : congrHom e ⁅z, g''⁆ = ⁅congrHom e z, congrHom e g''⁆ :=
            map_commutatorElement (congrHom e) z g''
          rw [← h2, ← hO]
          exact Subgroup.mem_map_of_mem _ (hzc g'' hg''))
      have h2 : congrHom e (t * z * t⁻¹ * z) =
          congrHom e t * congrHom e z * (congrHom e t)⁻¹ * congrHom e z := by
        rw [map_mul, map_mul, map_mul, map_inv]
      rw [← h2, ← hO] at h1
      exact hmem.1 h1

theorem MB4bc.of_std {Hs Xs : Subgroup (MulAut W)} {U : Subgroup W} {P : Subgroup (MulAut W)}
    {B : Subgroup W} (hU : fixV Xs = U) (hP : perfectCore (Hs ⊓ stabSub U) = P)
    (hB : s828BPrime Hs Xs = B)
    (hb : ∃ z ∈ P, z ^ 3 = 1 ∧ (∀ g ∈ P, ⁅z, g⁆ ∈ pCoreOf 2 P) ∧ ∃ b ∈ B, z b * b⁻¹ ∉ U)
    (hc : ∀ S : Subgroup (MulAut W), S ≤ Hs ⊓ stabSub U → IsPGroup 2 ↥S →
      ¬ 2 ∣ (S.subgroupOf (Hs ⊓ stabSub U)).index →
        ∃ t ∈ S, t ^ 2 = 1 ∧ (∃ g ∈ Hs, g * t * g⁻¹ ∈ Xs) ∧
          ∀ z ∈ P, (∀ g ∈ P, ⁅z, g⁆ ∈ pCoreOf 2 P) → t * z * t⁻¹ * z ∈ pCoreOf 2 P) :
    MB4bc Hs Xs := by
  subst hU hB hP
  exact ⟨hb, hc⟩

theorem mb4bc_of_map' (e : V ≃* W) (H X : Subgroup (MulAut V)) (Hs Xs : Subgroup (MulAut W))
    (hH : H.map (congrHom e) = Hs) (hX : X.map (congrHom e) = Xs) (h : MB4bc Hs Xs) :
    MB4bc H X := by
  subst hH hX
  exact mb4bc_of_map e H X h

end Transport

end CFSG.Quasithin.H13.Mat
