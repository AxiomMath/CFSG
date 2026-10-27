module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtIdx
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.IrrSec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42B1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtStep4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S42Gt

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

theorem Sit.exists_dtrans_elem (hs : Sit H M S α a₂ a₃ β) {θ : ↥(stab α) →* Perm (Fin 5)}
    (hθs : Function.Surjective θ) (hθk : ∀ x : ↥(stab α), θ x = 1 ↔ (x : G) ∈ Qv α)
    (hex : ∃ s ∈ stab α ⊓ stab β,
      s ∈ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) ∧ s ∉ Qv α) :
    ∃ w ∈ stab α ⊓ stab β, w ∈ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) ∧
      ∃ hw : w ∈ stab α, θ ⟨w, hw⟩ ≠ 1 ∧ θ ⟨w, hw⟩ ^ 2 = 1 ∧ Perm.sign (θ ⟨w, hw⟩) = 1 := by
  have hA := hs.amalg
  have hSyl : IsSylowTwoOf (stab α ⊓ stab β) (stab α) := sylow_stab_inf_left hA hs.n₀
  have hP8 : Nat.card (((stab α ⊓ stab β).subgroupOf (stab α)).map θ) = 8 :=
    card_image_sylow hθs hSyl
  have hNP : (((stab α ⊓ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G)
        : Subgroup G).subgroupOf (stab α)).map θ) ≤
      ((stab α ⊓ stab β).subgroupOf (stab α)).map θ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have hN0 : (((stab α ⊓ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G)
        : Subgroup G).subgroupOf (stab α)).map θ) ≠ ⊥ := by
    intro hb
    obtain ⟨s, hsS, hsC, hsQ⟩ := hex
    have : θ ⟨s, hsS.1⟩ ∈ (((stab α ⊓ stab β ⊓ Subgroup.centralizer
        ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) : Subgroup G).subgroupOf (stab α)).map θ) :=
      ⟨⟨s, hsS.1⟩, Subgroup.mem_subgroupOf.mpr ⟨hsS, hsC⟩, rfl⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hsQ ((hθk _).mp this)
  have hnorm : ((stab α ⊓ stab β).subgroupOf (stab α)).map θ ≤ Subgroup.normalizer
      ((((stab α ⊓ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G)
        : Subgroup G).subgroupOf (stab α)).map θ : Subgroup (Perm (Fin 5))) :
        Set (Perm (Fin 5))) := by
    have key : ∀ p ∈ ((stab α ⊓ stab β).subgroupOf (stab α)).map θ,
        ∀ x ∈ (((stab α ⊓ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G)
          : Subgroup G).subgroupOf (stab α)).map θ),
        p * x * p⁻¹ ∈ (((stab α ⊓ stab β ⊓ Subgroup.centralizer
          ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) : Subgroup G).subgroupOf (stab α)).map θ) := by
      rintro _ ⟨s, hs', rfl⟩ _ ⟨w', hw', rfl⟩
      have hs'' : (s : G) ∈ stab α ⊓ stab β := Subgroup.mem_subgroupOf.mp hs'
      have hw'' := Subgroup.mem_subgroupOf.mp hw'
      have hsn := normalizer_le_normalizer_centralizer _ (hs.R_normal hs''.2)
      refine ⟨s * w' * s⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs'' hw''.1)
          (Subgroup.inv_mem _ hs'')
      · exact (Subgroup.mem_normalizer_iff.mp hsn (w' : G)).mp hw''.2
      · rw [map_mul, map_mul, map_inv]
    exact fun p hp => F53B3.O1.mem_normalizer_of_conj (fun x hx => key p hp x hx)
      (fun x hx => by simpa using key p⁻¹ (Subgroup.inv_mem _ hp) x hx)
  obtain ⟨z', hz'N, hz'1, hz'2, hz'sg⟩ :=
    exists_double_transposition_of_normal hP8 hNP hnorm hN0
  obtain ⟨w', hw', rfl⟩ := hz'N
  have hw'' := Subgroup.mem_subgroupOf.mp hw'
  exact ⟨w', hw''.1, hw''.2, w'.2, hz'1, hz'2, hz'sg⟩

theorem hss42Comm_gt_of_irr (hA : F53Amalgam H M S) (h28 : Hss28At H M) (hirr : IrrSec)
    {α β α' : Geo H M} (hc : IsCritData α β α') (hα : vtype α = false)
    (hz : ⁅Zv α, Zv α'⁆ = ⊥) (hb : 1 < bMin H M) :
    IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α) := by
  have hZβc : Zv β ≤ centerOf (stab β) := Zv_central_of_comm_eq_bot hA hc hz
  obtain ⟨-, hodd, hvt⟩ := hss114_ab hA hc hz hb
  have hb3 : 3 ≤ bMin H M := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hβn : β ∈ nbrs α := hc.adj
  have hαn : α ∈ nbrs β := hc.adj.symm
  have hvβ : vtype β = true := by
    cases h : vtype β
    · exact absurd (hα.trans h.symm) (vtype_ne_of_adj hc.adj)
    · rfl
  have hv' : vtype α' = true := hvt.trans hvβ
  obtain ⟨α₂, α₃, T⟩ := exists_tri hA hvβ hαn
  have hs : Sit H M S α α₂ α₃ β := ⟨hA, h28, hb, hc.adj, hα, hc.bAt_eq, hZβc, T⟩
  have hidx := hs.relIndex_Y_le_eight hb3 hc hv'
  have hTs : IsSylowTwoOf (stab α ⊓ stab β) (stab α) := sylow_stab_inf_left hA hβn
  have hcent := EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_inf_centralizer_edge_eq hA
    hc.adj hZβc
  have hZβ : Zv β = quasithinOmegaOneCenter (stab α ⊓ stab β) := by
    rw [inf_comm]; exact (Zv_eq_omegaOneCenter_inf hA hαn hZβc).1
  have hcen0 : centerOf (stab α) = ⊥ := centerOf_eq_bot_of_Zv_central hA hαn hZβc
  have hcen : stab α ⊓ Subgroup.centralizer (Zv α : Set G) = Qv α :=
    centralizer_Zv_eq_Qv_of_bAt hA hc.bAt_eq
  have hVC : Zv α ⊓ Subgroup.centralizer (stab α : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hcen0]
    exact fun x hx => ⟨pCoreOf_le 2 _ (Zv_le_Qv hA α hx.1), hx.2⟩
  have hgen : ∀ U : Subgroup G, U ≤ Zv α → stab α ≤ Subgroup.normalizer (U : Set G) →
      Zv α ⊓ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) ≤ U → U = Zv α := by
    intro U hUV hUn hle
    refine le_antisymm hUV ?_
    have hβK : Zv β ≤ U := hcent ▸ hle
    rw [Zv_eq_conjClosure hTs, ← hZβ]
    refine (Subgroup.closure_le U).mpr ?_
    rintro _ ⟨g, hg, z, hz', rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hUn hg) z).mp (hβK hz')
  obtain ⟨n, θ, hn5, hθs, hθk⟩ := exists_quotHom hA α
  have hn5' : n = 5 := by
    rcases hn5 with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · rw [hα] at h; exact absurd h (by decide)
  subst hn5'
  obtain ⟨w, hwS, hwC, hwα, hθ1, hθ2, hθsg⟩ :=
    hs.exists_dtrans_elem hθs hθk (hs.exists_mem_C hb3)
  have hker : θ.ker = (cSecIn (stab α) ⊥ (Zv α)).subgroupOf (stab α) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, cSecIn_bot_eq, hcen]
    exact hθk x
  have hmem : w ∈ oTwoRes (stab α) ⊔ pCoreOf 2 (stab α) := by
    have := (mem_oTwoRes_sup_iff (L := ⊥) (X := Zv α) hθs hker hwα).mpr
      ((Equiv.Perm.mem_alternatingGroup).mpr hθsg)
    rwa [cSecIn_bot_eq, hcen] at this
  have hY : Zv α ⊓ Zv α₂ ≤ Zv α ⊓ Subgroup.centralizer ({w} : Set G) := fun y hy =>
    ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hwC y hy)⟩
  have hidx' : (Zv α ⊓ Subgroup.centralizer ({w} : Set G)).relIndex (Zv α) ≤ 8 :=
    (Subgroup.relIndex_le_of_le_left hY Subgroup.index_ne_zero_of_finite).trans hidx
  refine hirr G (stab α) (Zv α) (stab α ⊓ stab β) (quot_stab_five hA hα)
    (Zv_le_Qv hA α) (stab_le_normalizer_Zv hA α) (isElemAbelian_Zv hA α) hcen
    hVC hTs hgen w hmem ?_ (Or.inl ?_) hidx'
  · intro hwQ
    exact hθ1 ((hθk ⟨w, hwα⟩).mpr hwQ)
  · have : θ (⟨w, hwα⟩ ^ 2) = 1 := by rw [map_pow]; exact hθ2
    exact (hθk _).mp this

end S42Gt

open S42Gt

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss42Comm_gt (hA : F53Amalgam H M S) (h28 : Hss28At H M) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hα : vtype α = false) (hz : ⁅Zv α, Zv α'⁆ = ⊥)
    (hb : 1 < bMin H M) : IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α) :=
  hss42Comm_gt_of_irr hA h28 EmptyFaithful.Stellmacher.OrdinaryProofs.irrSec hc hα hz hb

end F53.Stellmacher

end CFSG.Quasithin
