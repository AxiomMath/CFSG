module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

/-!
## Proposition 1.2: Baer intersection + chief-factor centralizers
-/

section ChiefFactorQuotient

variable {G : Type*} [Group G]

namespace CFSG.ChiefFactor

/-- Pull back a chief factor along the quotient map `G → G ⧸ N`.
If `cf` is a chief factor of `G ⧸ N`, then its preimage under the quotient map is a chief factor of `G`. -/
@[expose]
public def comapMk' (N : Subgroup G) [N.Normal] (cf : ChiefFactor (G ⧸ N)) : ChiefFactor G :=
  { V := cf.V.comap (QuotientGroup.mk' N)
    U := cf.U.comap (QuotientGroup.mk' N)
    isChief :=
      { normal_K := cf.isChief.normal_K.comap (QuotientGroup.mk' N)
        normal_H := cf.isChief.normal_H.comap (QuotientGroup.mk' N)
        lt := by
          classical
          -- Strictness follows from injectivity of `comap` along a surjection.
          have hle :
              cf.V.comap (QuotientGroup.mk' N) ≤ cf.U.comap (QuotientGroup.mk' N) :=
            Subgroup.comap_mono (le_of_lt cf.isChief.lt)
          have hne :
              cf.V.comap (QuotientGroup.mk' N) ≠ cf.U.comap (QuotientGroup.mk' N) := by
            intro h
            have hinj :
                Function.Injective (Subgroup.comap (QuotientGroup.mk' N : G →* G ⧸ N)) :=
              Subgroup.comap_injective (f := (QuotientGroup.mk' N : G →* G ⧸ N))
                (QuotientGroup.mk'_surjective N)
            have : cf.V = cf.U := hinj h
            exact (ne_of_lt cf.isChief.lt) this
          exact lt_of_le_of_ne hle hne
        is_maximal := by
          classical
          intro K hKnorm hVK hKU
          -- Move to the quotient, apply maximality, then pull back.
          let π : G →* G ⧸ N := QuotientGroup.mk' N
          have hπ_surj : Function.Surjective π := QuotientGroup.mk'_surjective N
          have hNleK : N ≤ K := by
            -- `N ≤ V.comap π ≤ K`.
            intro n hn
            have : (n : G) ∈ cf.V.comap π := by
              -- `π n = 1 ∈ cf.V`.
              have hπn : π n = 1 := (QuotientGroup.eq_one_iff (N := N) n).2 hn
              simp [π, Subgroup.mem_comap, hπn]
            exact hVK this
          let _ : (K.map π).Normal := hKnorm.map π hπ_surj
          have hV_le_map : cf.V ≤ K.map π := by
            have : (cf.V.comap π).map π ≤ K.map π := Subgroup.map_mono hVK
            simpa [Subgroup.map_comap_eq_self_of_surjective (f := π) hπ_surj cf.V] using this
          have hmap_le_U : K.map π ≤ cf.U := by
            have : K.map π ≤ (cf.U.comap π).map π := Subgroup.map_mono hKU
            simpa [Subgroup.map_comap_eq_self_of_surjective (f := π) hπ_surj cf.U] using this
          rcases cf.isChief.is_maximal (K.map π) (by infer_instance) hV_le_map hmap_le_U with h | h
          · left
            -- Pull back `K.map π = cf.V`.
            have hcomap : (K.map π).comap π = cf.V.comap π := congrArg (fun L => L.comap π) h
            -- Since `N ≤ K`, `comap (map K) = K`.
            have hK' : (K.map π).comap π = K :=
              Subgroup.comap_map_eq_self (f := π) (H := K) (by
                -- `ker π = N ≤ K`
                simpa [π] using hNleK)
            simpa [hK'] using hcomap
          · right
            have hcomap : (K.map π).comap π = cf.U.comap π := congrArg (fun L => L.comap π) h
            have hK' : (K.map π).comap π = K :=
              Subgroup.comap_map_eq_self (f := π) (H := K) (by
                simpa [π] using hNleK)
            simpa [hK'] using hcomap } }

end CFSG.ChiefFactor

end ChiefFactorQuotient

section BaerIntersection

variable {G : Type*} [Group G]

/-- The Baer intersection: intersection of centralizers of all chief factors (in the ambient group).
This is the subgroup `⋂_{cf} C_G(cf)`, where `cf` runs over all chief factors of `G`. -/
@[expose]
public def CFSG.baer (G : Type*) [Group G] : Subgroup G :=
  ⨅ cf : ChiefFactor G, centralizerOfChiefFactor (G := G) ⊤ cf


/-- The image of the Baer intersection under a quotient map is contained in the Baer intersection of the quotient group. -/
theorem CFSG.baer_map_mk'_le {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (baer (G := G)).map (QuotientGroup.mk' N) ≤ baer (G := G ⧸ N) := by
  classical
  -- Elementwise: pull back chief factors along the quotient map.
  refine le_iInf (fun cf => ?_)
  intro x hx
  rcases Subgroup.mem_map.1 hx with ⟨g, hg, rfl⟩
  -- Use that `g` centralizes the pulled-back chief factor.
  have hg' :
      g ∈ centralizerOfChiefFactor (G := G) ⊤ (ChiefFactor.comapMk' (G := G) N cf) :=
    (Subgroup.mem_iInf).1 hg (ChiefFactor.comapMk' (G := G) N cf)
  -- Now check the defining commutator condition in the quotient.
  refine (mem_centralizerOfChiefFactor (H := (⊤ : Subgroup (G ⧸ N))) (cf := cf) (g := (QuotientGroup.mk' N) g)).2 ?_
  refine ⟨by simp, ?_⟩
  intro u hu
  -- Choose a representative `u0 : G` for `u`.
  obtain ⟨u0, rfl⟩ := QuotientGroup.mk'_surjective N u
  have hu0 : u0 ∈ (ChiefFactor.comapMk' (G := G) N cf).U := by
    -- `u ∈ cf.U` iff `u0 ∈ cf.U.comap π`.
    simpa [ChiefFactor.comapMk', Subgroup.mem_comap] using hu
  have hcomm0 :
      ⁅g, u0⁆ ∈ (ChiefFactor.comapMk' (G := G) N cf).V :=
    (mem_centralizerOfChiefFactor (H := (⊤ : Subgroup G)) (cf := ChiefFactor.comapMk' (G := G) N cf) (g := g)).1 hg' |>.2 u0 hu0
  -- Push the commutator membership forward to the quotient.
  have : (QuotientGroup.mk' N) (⁅g, u0⁆) ∈ cf.V := by
    simpa [ChiefFactor.comapMk', Subgroup.mem_comap] using hcomm0
  -- Finish by rewriting the commutator in the quotient.
  simpa [map_commutatorElement] using this

end BaerIntersection

section BaerIntersectionFinite

universe u

variable {G : Type*} [Group G]

/-- Given a minimal nontrivial normal subgroup `M`, produce the chief factor `⊥ < M`. -/
@[expose]
public def CFSG.chiefFactorBot (M : Subgroup G) (hM : M.Normal) (hM_ne_bot : M ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ M → K ≠ ⊥ → K = M) : ChiefFactor G :=
  { V := ⊥
    U := M
    isChief :=
      { normal_K := by infer_instance
        normal_H := hM
        lt := bot_lt_iff_ne_bot.2 hM_ne_bot
        is_maximal := by
          intro K hKnorm _hbot hKM
          by_cases hKbot : K = ⊥
          · left; exact hKbot
          · right
            exact hmin K hKnorm hKM hKbot } }

@[simp] public theorem CFSG.chiefFactorBot_V (M : Subgroup G) (hM : M.Normal) (hM_ne_bot : M ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ M → K ≠ ⊥ → K = M) :
    (chiefFactorBot (G := G) M hM hM_ne_bot hmin).V = ⊥ := rfl

@[simp] public theorem CFSG.chiefFactorBot_U (M : Subgroup G) (hM : M.Normal) (hM_ne_bot : M ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ M → K ≠ ⊥ → K = M) :
    (chiefFactorBot (G := G) M hM hM_ne_bot hmin).U = M := rfl

/-- The Baer intersection centralizes every minimal nontrivial normal subgroup. -/
theorem CFSG.baer_le_centralizer_of_minimalNormal (M : Subgroup G) (hM : M.Normal) (hM_ne_bot : M ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ M → K ≠ ⊥ → K = M) :
    baer (G := G) ≤ Subgroup.centralizer (M : Set G) := by
  classical
  let cf : ChiefFactor G := chiefFactorBot (G := G) M hM hM_ne_bot hmin
  have hle : baer (G := G) ≤ centralizerOfChiefFactor (G := G) ⊤ cf :=
    iInf_le (fun cf : ChiefFactor G => centralizerOfChiefFactor (G := G) ⊤ cf) cf
  have hcomm : ⁅baer (G := G), cf.U⁆ ≤ cf.V := by
    have := (le_centralizerOfChiefFactor_iff (G := G) (H := (⊤ : Subgroup G)) (N := baer (G := G)) (cf := cf)).1 hle
    simpa using this.2
  have hcomm' : ⁅baer (G := G), M⁆ = ⊥ := by
    apply le_bot_iff.mp
    simpa [cf, chiefFactorBot] using hcomm
  -- `⁅baer, M⁆ = ⊥` means `baer ≤ C_G(M)`.
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := baer (G := G)) (H₂ := M)).1 hcomm'

/-- In a finite solvable nontrivial group, there exists a nontrivial abelian normal subgroup. -/
private theorem CFSG.exists_nontrivial_abelian_normal (hsolv : Group.IsSolvable G) (hnt : Nontrivial G) :
    ∃ (N : Subgroup G), N.Normal ∧ IsMulCommutative N ∧ N ≠ ⊥ := by
  classical
  let _ : Group.IsSolvable G := hsolv
  let p : Nat → Prop := fun n => derivedSeries G n = ⊥
  have hp : ∃ n, p n := (inferInstance : Group.IsSolvable G).solvable
  let i := Nat.find hp
  have hi : i ≠ 0 := by
    have : ¬ p 0 := by
      simp [p, derivedSeries_zero]
    exact (Nat.find_eq_zero hp).not.mpr this
  refine ⟨derivedSeries G (i - 1), derivedSeries_normal _ _, ?_, Nat.find_min hp (Nat.sub_one_lt hi)⟩
  refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  rw [← derivedSeries_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
  exact Nat.find_spec hp

variable [Finite G]

/-- In a finite solvable nontrivial group, there exists a minimal nontrivial normal subgroup. -/
public theorem CFSG.exists_minimal_normal (hsolv : Group.IsSolvable G) (hnt : Nontrivial G) :
    ∃ M : Subgroup G,
      M.Normal ∧ M ≠ ⊥ ∧
        (∀ K : Subgroup G, K.Normal → K ≤ M → K ≠ ⊥ → K = M) := by
  classical
  obtain ⟨N, hNnorm, _hNcomm, hNne⟩ := exists_nontrivial_abelian_normal (G := G) hsolv hnt
  rcases exists_minimal_normal_le (G := G) N hNnorm hNne with ⟨M, hMnorm, _hMN, hMne, hMmin⟩
  exact ⟨M, hMnorm, hMne, hMmin⟩

/-- If `N` is a nontrivial subgroup of a finite group, then `|G/N| < |G|`. -/
public theorem CFSG.card_quotient_lt_of_ne_bot (N : Subgroup G) (hN_ne_bot : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  classical
  have hN_one_lt : 1 < Nat.card (↥N) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := N)).2 hN_ne_bot
  -- `|G| = |G/N| * |N|`.
  have hcard : Nat.card G = Nat.card (G ⧸ N) * Nat.card (↥N) := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := N))
  -- Since `|N| > 1`, multiplication strictly increases.
  have : Nat.card (G ⧸ N) * 1 < Nat.card (G ⧸ N) * Nat.card (↥N) :=
    Nat.mul_lt_mul_of_pos_left hN_one_lt (Nat.card_pos (α := G ⧸ N))
  simpa [hcard] using this


/-- Baer's theorem (nilpotency part): the full Baer intersection is nilpotent in solvable groups.
Proved by induction on the cardinality of `G`. -/
public theorem CFSG.baer_nilpotent_of_card :
    ∀ n : ℕ, ∀ {G : Type u} [Group G] [Finite G],
      Nat.card G = n → Group.IsSolvable G → Group.IsNilpotent (baer (G := G)) := by
  intro n
  refine Nat.strongRecOn
    (motive := fun n =>
      ∀ {G : Type u} [Group G] [Finite G], Nat.card G = n → Group.IsSolvable G →
        Group.IsNilpotent (baer (G := G)))
    n (fun n ih => by
      intro G _instG _instF hcard hsolvG
      classical
      by_cases htriv : Nat.card G = 1
      · have hle : Nat.card G ≤ 1 := by simp [htriv]
        have _ : Subsingleton G := (Finite.card_le_one_iff_subsingleton (α := G)).1 hle
        infer_instance
      · have hpos : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
        have hone : 1 < Nat.card G :=
          Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hpos, htriv⟩
        have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 hone
        obtain ⟨M, hMnorm, hMne, hMmin⟩ := exists_minimal_normal (G := G) hsolvG hnt
        have hquot_lt' : Nat.card (G ⧸ M) < Nat.card G :=
          card_quotient_lt_of_ne_bot (G := G) M hMne
        have hquot_lt : Nat.card (G ⧸ M) < n := by simpa [hcard] using hquot_lt'
        let _ : Group.IsSolvable G := hsolvG
        have hsolvQ : Group.IsSolvable (G ⧸ M) := by infer_instance
        have hnilQ : Group.IsNilpotent (baer (G := G ⧸ M)) := by
          -- Keep the implicit `∀ {H}` binders explicit to avoid elaboration guessing.
          have h :
              ∀ {H : Type u} [Group H] [Finite H],
                Nat.card H = Nat.card (G ⧸ M) → Group.IsSolvable H → Group.IsNilpotent (baer (G := H)) :=
            ih (Nat.card (G ⧸ M)) hquot_lt
          exact @h (G ⧸ M) _ _ rfl hsolvQ
        let π : G →* G ⧸ M := QuotientGroup.mk' M
        have _ : M.Normal := hMnorm
        have hπ_mem : ∀ x : ↥(baer (G := G)), π x.1 ∈ baer (G := G ⧸ M) := by
          intro x
          have hxmap : π x.1 ∈ (baer (G := G)).map π := Subgroup.mem_map_of_mem π x.property
          exact (baer_map_mk'_le (G := G) M) hxmap
        let f : (↥(baer (G := G))) →* (↥(baer (G := G ⧸ M))) :=
          ((π.comp (baer (G := G)).subtype).codRestrict (baer (G := G ⧸ M)) (by
            intro x
            simpa using hπ_mem x))
        have hbaer_cent : baer (G := G) ≤ Subgroup.centralizer (M : Set G) :=
          baer_le_centralizer_of_minimalNormal (G := G) M hMnorm hMne hMmin
        have hker : f.ker ≤ Subgroup.center (↥(baer (G := G))) := by
          intro x hx
          have hx1 : π x.1 = 1 := by
            simpa [f, MonoidHom.mem_ker] using hx
          have hxM : (x : G) ∈ M := (QuotientGroup.eq_one_iff (N := M) x.1).1 hx1
          refine (Subgroup.mem_center_iff).2 ?_
          intro y
          have hy_cent : (y : G) ∈ Subgroup.centralizer (M : Set G) := hbaer_cent y.property
          have hy_comm : y.1 * x.1 = x.1 * y.1 :=
            ((Subgroup.mem_centralizer_iff).1 hy_cent x.1 (by simpa using hxM)).symm
          ext
          simpa using hy_comm
        exact Subgroup.isNilpotent_of_ker_le_center f hker)

/-- The Baer intersection of a finite solvable group is nilpotent. -/
public theorem CFSG.baer_nilpotent (hsolv : Group.IsSolvable G) :
    Group.IsNilpotent (baer (G := G)) :=
  baer_nilpotent_of_card (Nat.card G) (G := G) rfl hsolv

end BaerIntersectionFinite

section NilpotentCentralizesChiefFactor

variable {G : Type*} [Group G]

/-- A surjective homomorphism from a subgroup `N` to its image under a homomorphism `f`. -/
def CFSG.subgroupToMap {H : Type*} [Group H] (f : G →* H) (N : Subgroup G) :
    (↥N) →* (↥(N.map f)) :=
  (f.comp N.subtype).codRestrict (N.map f) (by
    intro x
    exact Subgroup.mem_map_of_mem f x.property)

/-- The homomorphism `subgroupToMap f N` is surjective. -/
theorem CFSG.subgroupToMap_surjective {H : Type*} [Group H] (f : G →* H) (N : Subgroup G) :
    Function.Surjective (subgroupToMap (G := G) f N) := by
  intro y
  -- Unpack `y.1 ∈ N.map f`.
  rcases (Subgroup.mem_map).1 y.property with ⟨x, hx, hx_eq⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  ext
  simp [subgroupToMap, hx_eq]

/-- If a subgroup `N` is nilpotent, then its image under a homomorphism is also nilpotent. -/
theorem CFSG.isNilpotent_map_of_isNilpotent {H : Type*} [Group H] (f : G →* H) (N : Subgroup G)
    (hN : Group.IsNilpotent N) :
    Group.IsNilpotent (↥(N.map f)) := by
  classical
  let φ := subgroupToMap (G := G) f N
  have hsurj : Function.Surjective φ := subgroupToMap_surjective (G := G) f N
  let _ : Group.IsNilpotent (↥N) := hN
  exact Group.nilpotent_of_surjective (G := (↥N)) (G' := (↥(N.map f))) φ hsurj

/-- For a chief factor `cf = (V ◁ U)`, the image `U/V` in the quotient `G/V` is a minimal nontrivial normal subgroup. -/
public theorem CFSG.chiefFactor_quotient_minimal (cf : ChiefFactor G) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    Uq.Normal ∧ Uq ≠ ⊥ ∧
      (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
  classical
  let _ : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hUq_ne_bot : Uq ≠ ⊥ := by
    intro hbot
    have hle : cf.U ≤ π.ker := (Subgroup.map_eq_bot_iff (f := π) (H := cf.U)).1 hbot
    -- `ker π = cf.V`.
    have hle' : cf.U ≤ cf.V := by
      simpa [π, QuotientGroup.ker_mk'] using hle
    have : cf.U = cf.V := le_antisymm hle' cf.isChief.lt.le
    exact (ne_of_lt cf.isChief.lt) this.symm
  let _ : Uq.Normal := (cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V))
  refine ⟨inferInstance, hUq_ne_bot, ?_⟩
  intro K hKnorm hKUq hK_ne_bot
  -- Pull back `K` to `G` and apply maximality of the chief factor.
  have hKcomap_norm : (K.comap π).Normal := hKnorm.comap π
  have hV_le_comap : cf.V ≤ K.comap π := by
    intro v hv
    have hv1 : π v = 1 := (QuotientGroup.eq_one_iff (N := cf.V) v).2 hv
    -- membership in the comap means `π v ∈ K`.
    show π v ∈ K
    simp [hv1]
  have hcomap_le_U : K.comap π ≤ cf.U := by
    have : K.comap π ≤ (Uq.comap π) := Subgroup.comap_mono hKUq
    -- `Uq.comap π = cf.U ⊔ cf.V = cf.U` since `cf.V ≤ cf.U`.
    have hUq_comap : Uq.comap π = cf.U := by
      have : (cf.U.map π).comap π = cf.U ⊔ π.ker := Subgroup.comap_map_eq (f := π) (H := cf.U)
      -- `π.ker = cf.V` and `cf.V ≤ cf.U`.
      simpa [Uq, π, QuotientGroup.ker_mk', sup_eq_left.2 cf.isChief.lt.le] using this
    simpa [hUq_comap] using this
  rcases cf.isChief.is_maximal (K.comap π) hKcomap_norm hV_le_comap hcomap_le_U with hKV | hKU
  · -- If `K.comap π = cf.V`, then `K = ⊥`, contradiction.
    have hKbot : K = ⊥ := by
      have hmap : (K.comap π).map π = K :=
        Subgroup.map_comap_eq_self_of_surjective (f := π) (QuotientGroup.mk'_surjective cf.V) K
      -- `cf.V.map π = ⊥`.
      have hVmap : (cf.V.map π) = ⊥ := by
        apply (Subgroup.map_eq_bot_iff (f := π) (H := cf.V)).2
        simp [π, QuotientGroup.ker_mk']
      -- Combine.
      -- `K = (K.comap π).map π = cf.V.map π = ⊥`.
      calc
        K = (K.comap π).map π := by simp [hmap]
        _ = (cf.V.map π) := by simp [hKV]
        _ = ⊥ := hVmap
    exact (hK_ne_bot hKbot).elim
  · -- Otherwise `K.comap π = cf.U`, so `K = Uq`.
    have hmap : (K.comap π).map π = K :=
      Subgroup.map_comap_eq_self_of_surjective (f := π) (QuotientGroup.mk'_surjective cf.V) K
    -- `cf.U.map π = Uq`.
    calc
      K = (K.comap π).map π := by simp [hmap]
      _ = (cf.U.map π) := by simp [hKU]
      _ = Uq := by simp [Uq]

/-- The quotient `U/V` attached to a chief factor is a minimal normal subgroup of `G/V`. -/
public theorem CFSG.chiefFactor_quotient_isMinimalNormal (cf : ChiefFactor G) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    IsMinimalNormal Uq := by
  classical
  let _ : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin := chiefFactor_quotient_minimal (G := G) cf
  have hUq_min :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using hmin
  let _ : Uq.Normal := hUq_min.1
  refine ⟨?_⟩
  intro K hKnorm hKUq
  by_cases hKbot : K = ⊥
  · exact Or.inl hKbot
  · exact Or.inr (hUq_min.2.2 K hKnorm hKUq hKbot)

variable [Finite G]

/-- In a finite solvable group, every chief factor quotient is elementary abelian. -/
public theorem CFSG.chiefFactor_quotient_exists_isElementaryAbelian (hsolv : Group.IsSolvable G)
    (cf : ChiefFactor G) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p (↥Uq) := by
  classical
  let _ : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin := chiefFactor_quotient_minimal (G := G) cf
  have hUq_min :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using hmin
  let _ : Uq.Normal := hUq_min.1
  have _ : IsMinimalNormal Uq := by
    simpa [π, Uq] using chiefFactor_quotient_isMinimalNormal (G := G) cf
  let _ : Group.IsSolvable (G ⧸ cf.V) := by
    let _ : Group.IsSolvable G := hsolv
    infer_instance
  let _ : Group.IsSolvable (↥Uq) := by infer_instance
  exact minimalNormal_solvable_exists_isElementaryAbelian (G := G ⧸ cf.V) Uq

/-- Any normal nilpotent subgroup of a finite solvable group centralizes every chief factor. -/
public theorem CFSG.normal_nilpotent_le_centralizerOfChiefFactor_top (hsolv : Group.IsSolvable G)
    (N : Subgroup G) (hN : N.Normal) (hN_nil : Group.IsNilpotent N) (cf : ChiefFactor G) :
    N ≤ centralizerOfChiefFactor (G := G) ⊤ cf := by
  classical
  let _ : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  -- `Uq` is minimal normal in the quotient.
  have hmin := chiefFactor_quotient_minimal (G := G) cf
  have hUq_min : Uq.Normal ∧ Uq ≠ ⊥ ∧
      (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using hmin
  -- Work in the quotient group `G ⧸ cf.V`.
  let _ : Group.IsSolvable G := hsolv
  let _ : Group.IsSolvable (G ⧸ cf.V) := by infer_instance
  let _ : Group.IsSolvable (↥Uq) := by infer_instance
  -- Apply Lemma 1.1 in the quotient to get centrality in the quotient Fitting subgroup.
  have hUq_centerIn :
      Uq ≤ centerIn (G := (G ⧸ cf.V)) (fittingSubgroup (G ⧸ cf.V)) := by
    let _ : Uq.Normal := hUq_min.1
    let _ : IsMinimalNormal Uq := {
        minimal := fun (K) [hKn : K.Normal] hle => by
          have := hUq_min.2.2 K hKn hle
          grind }
    exact minimalNormal_solvable_le_centerIn_fittingSubgroup
      (G := (G ⧸ cf.V)) (M := Uq)
  let Fq : Subgroup (G ⧸ cf.V) := fittingSubgroup (G ⧸ cf.V)
  have hUq_le_centF : Uq ≤ Subgroup.centralizer (Fq : Set (G ⧸ cf.V)) := by
    intro x hx
    have hx' : x ∈ centerIn (G := (G ⧸ cf.V)) Fq := hUq_centerIn hx
    dsimp [centerIn] at hx'
    exact hx'.2
  -- Hence `Fq` centralizes `Uq`.
  have hFq_le_centralizer : Fq ≤ Subgroup.centralizer (Uq : Set (G ⧸ cf.V)) :=
    (Subgroup.le_centralizer_iff (H := Uq) (K := Fq)).1 hUq_le_centF
  have hcomm_Fq_Uq : ⁅Fq, Uq⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Fq) (H₂ := Uq)).2 hFq_le_centralizer
  -- The image of `N` in the quotient lies in `Fq`.
  let _ : N.Normal := hN
  let _ : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective cf.V)
  have hNmap_nil : Group.IsNilpotent (↥(N.map π)) :=
    isNilpotent_map_of_isNilpotent (G := G) (H := (G ⧸ cf.V)) π N hN_nil
  have hNmap_le_Fq : N.map π ≤ Fq := by
    -- `Fq` is the supremum of all normal nilpotent subgroups.
    exact le_sSup ⟨inferInstance, hNmap_nil⟩
  have hcomm_Nq_Uq : ⁅N.map π, Uq⁆ = ⊥ := by
    apply le_bot_iff.mp
    have : ⁅N.map π, Uq⁆ ≤ ⁅Fq, Uq⁆ := Subgroup.commutator_mono hNmap_le_Fq (le_rfl)
    simpa [hcomm_Fq_Uq] using this
  -- Pull the commutator statement back to `G`.
  have hcomm_map : (⁅N, cf.U⁆).map π = ⊥ := by
    calc
      (⁅N, cf.U⁆).map π = ⁅N.map π, cf.U.map π⁆ := by
        simpa using (Subgroup.map_commutator (H₁ := N) (H₂ := cf.U) π)
      _ = ⊥ := by simpa [Uq] using hcomm_Nq_Uq
  have hcomm_le_ker : ⁅N, cf.U⁆ ≤ π.ker :=
    (Subgroup.map_eq_bot_iff (f := π) (H := ⁅N, cf.U⁆)).1 hcomm_map
  have hcomm_le_V : ⁅N, cf.U⁆ ≤ cf.V := by
    simpa [π, QuotientGroup.ker_mk'] using hcomm_le_ker
  -- Conclude using `le_centralizerOfChiefFactor_iff`.
  have : N ≤ centralizerOfChiefFactor (G := G) ⊤ cf := by
    refine (le_centralizerOfChiefFactor_iff (G := G) (H := (⊤ : Subgroup G)) (N := N) (cf := cf)).2 ?_
    exact ⟨by simp, hcomm_le_V⟩
  simpa using this

end NilpotentCentralizesChiefFactor
