module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] [Finite G]

private lemma borel86_group_conj_subgroupOf_map {G : Type} [Group G] {L Q : Subgroup G}
    (hQ : Q ≤ L) {l : ↥L} :
    ((Q.subgroupOf L).map (MulAut.conj l)).map L.subtype =
      Q.map (MulAut.conj (l : G)) := by
  have hcomp : (L.subtype.comp (MulAut.conj l : ↥L →* ↥L) : ↥L →* G) =
      ((MulAut.conj (l : G) : G →* G).comp L.subtype : ↥L →* G) := by
    ext x
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hQ]

theorem exists_mem_normalizer_inf_not_fix {H K T : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ normalizer (K : Set G)) (hT : IsSylowIn 2 T H) {S : Type} [Group S]
    {ψ : ↥K →* S} (hsurj : Function.Surjective ψ) {ρ : ↥H →* MulAut S}
    (hact : ∀ (h : ↥H) (k x : ↥K), (x : G) = h * k * h⁻¹ → ρ h (ψ k) = ψ x) {t₀ : S}
    (hfixT : ∀ h : ↥H, (h : G) ∈ T → ρ h t₀ = t₀)
    (hborel : ∀ P : Sylow 2 S, (∀ p ∈ (P : Subgroup S), p * t₀ = t₀ * p) →
      ∃ d ∈ normalizer ((P : Subgroup S) : Set S), d * t₀ * d⁻¹ ≠ t₀) :
    ∃ y : ↥H, (y : G) ∈ normalizer ((T ⊓ (K ⊔ ρ.ker.map H.subtype) : Subgroup G) : Set G) ∧
      ρ y t₀ ≠ t₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite S := Finite.of_surjective ψ hsurj
  have hρK : ∀ k : ↥K, ρ ⟨k, hKH k.2⟩ = MulAut.conj (ψ k) := by
    intro k
    ext s
    obtain ⟨x, rfl⟩ := hsurj s
    let x' : ↥K := ⟨(k : G) * (x : G) * (k : G)⁻¹, by
      have hkH : (k : G) ∈ H := hKH k.2
      exact (Subgroup.mem_normalizer_iff.mp (hKn hkH) (x : G)).mp x.2⟩
    have heq : (x' : G) = (⟨k, hKH k.2⟩ : ↥H) * x * (⟨k, hKH k.2⟩ : ↥H)⁻¹ := rfl
    have h := hact ⟨k, hKH k.2⟩ x x' heq
    rw [h]
    have hx' : x' = k * x * k⁻¹ := Subtype.ext rfl
    rw [hx', map_mul, map_mul, map_inv]
    rfl
  let Z : Subgroup G := ρ.ker.map H.subtype
  let Y : Subgroup G := K ⊔ Z
  have hZH : Z ≤ H := by
    intro z hz
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hz
    exact h.2
  have hYH : Y ≤ H := sup_le hKH hZH
  have hZsub : Z.subgroupOf H = ρ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, hhx⟩
      have hx : h = x := Subtype.ext hhx
      rwa [hx] at hh
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hZn : H ≤ normalizer (Z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZH).mp (by
      rw [hZsub]
      exact MonoidHom.normal_ker ρ)
  have hKn' : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hYn : H ≤ normalizer (Y : Set G) :=
    le_trans (le_inf hKn hZn) (Subgroup.inf_normalizer_le_normalizer_sup K Z)
  have hYN : (Y.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr hYn
  let Q : Subgroup G := T ⊓ Y
  have hQY : IsSylowIn 2 Q Y := IsSylowIn.inf_normal hT hYH hYN
  have hQK : IsSylowIn 2 (T ⊓ K) K := IsSylowIn.inf_normal hT hKH hKn'
  let P₀ : Sylow 2 S := (hQK.toSylow).mapSurjective hsurj
  have hP₀coe : (P₀ : Subgroup S) = ((T ⊓ K).subgroupOf K).map ψ := by
    change ((hQK.toSylow).mapSurjective hsurj : Subgroup S) =
      ((T ⊓ K).subgroupOf K).map ψ
    rw [Sylow.coe_mapSurjective hsurj (hQK.toSylow), IsSylowIn.coe_toSylow]
  have hP₀c : ∀ p ∈ (P₀ : Subgroup S), p * t₀ = t₀ * p := by
    intro p hp
    rw [hP₀coe] at hp
    obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.mp hp
    have hkT : (k : G) ∈ T := (Subgroup.mem_subgroupOf.mp hk).1
    have hfix : ψ k * t₀ * (ψ k)⁻¹ = t₀ := by
      have h1 := hfixT ⟨k, hKH k.2⟩ hkT
      rwa [hρK k, MulAut.conj_apply] at h1
    rw [← hkp]
    calc ψ k * t₀ = ψ k * t₀ * (ψ k)⁻¹ * ψ k := by group
      _ = t₀ * ψ k := by rw [hfix]
  obtain ⟨d, hdN, hdt⟩ := hborel P₀ hP₀c
  obtain ⟨k₁, hk₁⟩ := hsurj d
  have hρk₁ : ρ ⟨k₁, hKH k₁.2⟩ = MulAut.conj d := by rw [hρK k₁, hk₁]
  let Inn : Subgroup (MulAut S) := CFSG.ComponentClassification.OuterAutomorphisms.inner S
  let φ : S →* Inn := (MulAut.conj : S →* MulAut S).rangeRestrict
  have hφsurj : Function.Surjective φ :=
    (MulAut.conj : S →* MulAut S).rangeRestrict_surjective
  let P : Sylow 2 Inn := P₀.mapSurjective hφsurj
  let I : Subgroup (MulAut S) := (P : Subgroup Inn).map Inn.subtype
  have hPcoe : (P : Subgroup Inn) = (P₀ : Subgroup S).map φ :=
    Sylow.coe_mapSurjective hφsurj P₀
  have hcomp : Inn.subtype.comp φ = (MulAut.conj : S →* MulAut S) := by ext s; rfl
  have hIeq : I = (P₀ : Subgroup S).map (MulAut.conj : S →* MulAut S) := by
    change (P : Subgroup Inn).map Inn.subtype =
      (P₀ : Subgroup S).map (MulAut.conj : S →* MulAut S)
    rw [hPcoe, Subgroup.map_map, hcomp]
  have hIinner : I ≤ Inn := by
    rw [hIeq]
    exact Subgroup.map_le_range (f := (MulAut.conj : S →* MulAut S)) (P₀ : Subgroup S)
  let R : Subgroup (MulAut S) := (Q.subgroupOf H).map ρ
  have hKcomap : K.subgroupOf H ≤ Inn.comap ρ := by
    intro x hx
    rw [Subgroup.mem_comap]
    let k : ↥K := ⟨(x : G), hx⟩
    have hxeq : x = ⟨k, hKH k.2⟩ := Subtype.ext rfl
    rw [hxeq, hρK k]
    exact ⟨ψ k, rfl⟩
  have hZcomap : Z.subgroupOf H ≤ Inn.comap ρ := by
    rw [hZsub]
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact Subgroup.one_mem _
  have hYcomap : Y.subgroupOf H ≤ Inn.comap ρ := by
    rw [show Y = K ⊔ Z from rfl, Subgroup.subgroupOf_sup hKH hZH]
    exact sup_le hKcomap hZcomap
  have hQYH : Q.subgroupOf H ≤ Y.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hx.2
  have hQinner : R ≤ Inn :=
    (Subgroup.map_le_iff_le_comap).mpr (hQYH.trans hYcomap)
  have hR2 : IsPGroup 2 R := hQY.isPGroup.comap_subtype (K := H) |>.map ρ
  have hIleR : I ≤ R := by
    rw [hIeq]
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hP₀coe] at hp
    obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.mp hp
    refine Subgroup.mem_map.mpr ⟨⟨k, hKH k.2⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr
        ⟨(Subgroup.mem_subgroupOf.mp hk).1, Subgroup.mem_sup_left k.2⟩
    · rw [hρK k, hkp]
  have hIsub : I.subgroupOf Inn = P := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    change (x : MulAut S) ∈ (P : Subgroup Inn).map Inn.subtype ↔ x ∈ P
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyeq : y = x := Subtype.ext hyx
      rwa [hyeq] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hsub : R.subgroupOf Inn = I.subgroupOf Inn := by
    refine (P.is_maximal' ?_ ?_).trans hIsub.symm
    · exact hR2.comap_subtype (K := Inn)
    · rw [hPcoe]
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have hsI : MulAut.conj s ∈ I := by
        rw [hIeq]
        exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
      change (φ s : MulAut S) ∈ R
      exact hIleR hsI
  have hRmap : (R.subgroupOf Inn).map Inn.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le hQinner
  have hImap : (I.subgroupOf Inn).map Inn.subtype = I :=
    Subgroup.map_subgroupOf_eq_of_le hIinner
  have hRI : R = I := by rw [← hRmap, hsub, hImap]
  let L : Subgroup G := Y ⊓ (I.comap ρ).map H.subtype
  have hQL : Q ≤ L := by
    intro q hq
    have hqY : q ∈ Y := hq.2
    have hqH : q ∈ H := hYH hqY
    refine Subgroup.mem_inf.mpr ⟨hqY, ?_⟩
    refine Subgroup.mem_map.mpr ⟨⟨q, hqH⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    have hmemR : ρ ⟨q, hqH⟩ ∈ R := by
      refine Subgroup.mem_map.mpr ⟨⟨q, hqH⟩, ?_, rfl⟩
      exact hq
    rwa [hRI] at hmemR
  have hLY : L ≤ Y := inf_le_left
  have hQsylowL : IsSylowIn 2 Q L := by
    refine ⟨hQL, hQY.isPGroup, ?_⟩
    intro h2
    apply hQY.not_dvd_relIndex
    have hdvd : 2 ∣ Q.relIndex L * L.relIndex Y := dvd_mul_of_dvd_left h2 _
    rwa [Subgroup.relIndex_mul_relIndex Q L Y hQL hLY] at hdvd
  have hconj : ∀ x ∈ L, (k₁ : G) * x * (k₁ : G)⁻¹ ∈ L := by
    intro x hx
    have hxY : x ∈ Y := hx.1
    have hxH : x ∈ H := hYH hxY
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx.2
    have haeq : a = ⟨x, hxH⟩ := Subtype.ext hax
    have hxI : ρ ⟨x, hxH⟩ ∈ I := by
      rw [← haeq]
      exact Subgroup.mem_comap.mp ha
    obtain ⟨p, hp, hpx⟩ : ∃ p ∈ (P₀ : Subgroup S), MulAut.conj p = ρ ⟨x, hxH⟩ := by
      rw [hIeq] at hxI
      exact Subgroup.mem_map.mp hxI
    have hkxH : (k₁ : G) * x * (k₁ : G)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hKH k₁.2) hxH) (H.inv_mem (hKH k₁.2))
    have heq : (⟨(k₁ : G) * x * (k₁ : G)⁻¹, hkxH⟩ : ↥H) =
        ⟨k₁, hKH k₁.2⟩ * ⟨x, hxH⟩ * ⟨k₁, hKH k₁.2⟩⁻¹ := Subtype.ext rfl
    have hmem : ρ ⟨(k₁ : G) * x * (k₁ : G)⁻¹, hkxH⟩ ∈ I := by
      rw [heq, map_mul, map_mul, map_inv, hρk₁, ← hpx, hIeq]
      exact Subgroup.mem_map.mpr
        ⟨d * p * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdN p).mp hp,
          by simp [map_mul, map_inv]⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hYn (hKH k₁.2)) x).mp hxY
    · exact Subgroup.mem_map.mpr ⟨⟨_, hkxH⟩, Subgroup.mem_comap.mpr hmem, rfl⟩
  have hk₁L : (k₁ : G) ∈ normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hconj x hx
    · exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj (k₁ : G)).injective).symm
  have hLmap : L.map (MulAut.conj (k₁ : G)) = L :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hk₁L
  let Q' : Subgroup G := Q.map (MulAut.conj (k₁ : G))
  have hQ'L : IsSylowIn 2 Q' L := by
    refine ⟨?_, hQY.isPGroup.map _, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact hconj q (hQL hq)
    · have hrel : Q'.relIndex L = Q.relIndex L := by
        have h1 := Subgroup.relIndex_map_map_of_injective
          (f := (MulAut.conj (k₁ : G) : G →* G)) Q L
          (MulAut.conj (k₁ : G)).injective
        rwa [hLmap] at h1
      rw [hrel]
      exact hQsylowL.not_dvd_relIndex
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq (↥L) hQ'L.toSylow hQsylowL.toSylow
  have hlsub : (Q'.subgroupOf L).map (MulAut.conj l) = Q.subgroupOf L := by
    have h := congrArg (fun S : Sylow 2 ↥L => (S : Subgroup ↥L)) hl
    rw [Sylow.coe_subgroup_smul] at h
    rw [IsSylowIn.coe_toSylow, IsSylowIn.coe_toSylow] at h
    exact h
  have hlG : Q'.map (MulAut.conj (l : G)) = Q := by
    have h := congrArg (fun S : Subgroup ↥L => S.map L.subtype) hlsub
    rw [borel86_group_conj_subgroupOf_map hQ'L.le,
        Subgroup.map_subgroupOf_eq_of_le hQL] at h
    exact h
  have hQy : Q.map (MulAut.conj ((l : G) * (k₁ : G))) = Q := by
    rw [map_mul]
    change Q.map (((MulAut.conj (l : G) : G →* G)).comp
      (MulAut.conj (k₁ : G) : G →* G)) = Q
    rw [← Subgroup.map_map]
    exact hlG
  have hyN : ((l : G) * (k₁ : G)) ∈ normalizer (Q : Set G) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hQy
  have hlH : (l : G) ∈ H := hYH (hLY l.2)
  let yH : ↥H := ⟨(l : G) * (k₁ : G), H.mul_mem hlH (hKH k₁.2)⟩
  have hyH_eq : yH = ⟨l, hlH⟩ * ⟨k₁, hKH k₁.2⟩ := Subtype.ext rfl
  have hlI : ρ ⟨l, hlH⟩ ∈ I := by
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp l.2.2
    have haeq : a = ⟨l, hlH⟩ := Subtype.ext hax
    rw [← haeq]
    exact Subgroup.mem_comap.mp ha
  obtain ⟨p, hp, hlp⟩ : ∃ p ∈ (P₀ : Subgroup S), MulAut.conj p = ρ ⟨l, hlH⟩ := by
    rw [hIeq] at hlI
    exact Subgroup.mem_map.mp hlI
  have hρy : ρ yH t₀ = MulAut.conj p (MulAut.conj d t₀) := by
    rw [hyH_eq, map_mul, hρk₁, ← hlp]
    rfl
  have hyfix : ρ yH t₀ ≠ t₀ := by
    intro hfix
    have h2 : MulAut.conj p (MulAut.conj d t₀) = t₀ := by rw [← hρy]; exact hfix
    have h3 : MulAut.conj d t₀ = t₀ := by
      have h4 := congrArg (fun z => (MulAut.conj p)⁻¹ z) h2
      rw [MulAut.inv_apply_self, MulAut.conj_inv_apply] at h4
      have hpfix : p⁻¹ * t₀ * p = t₀ := by
        calc p⁻¹ * t₀ * p = p⁻¹ * (t₀ * p) := by group
          _ = p⁻¹ * (p * t₀) := by rw [← hP₀c p hp]
          _ = t₀ := by group
      rw [hpfix] at h4
      exact h4
    rw [MulAut.conj_apply] at h3
    exact hdt h3
  exact ⟨yH, by simpa [yH, Q, Y, Z] using hyN, hyfix⟩

theorem mul_mem_range_conj_of_isCyclic_map {S : Type} [Group S] [Finite S]
    (hS : ∀ B : Subgroup (MulAut S), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner S))))
    {α β : MulAut S} (hα : α * α = 1) (hβ : β * β = 1) (hαβ : α * β = β * α)
    (hαo : α ∉ (MulAut.conj : S →* MulAut S).range)
    (hβo : β ∉ (MulAut.conj : S →* MulAut S).range) :
    α * β ∈ (MulAut.conj : S →* MulAut S).range := by
  classical
  let B : Subgroup (MulAut S) := Subgroup.closure ({α, β} : Set (MulAut S))
  have hαB : α ∈ B := Subgroup.subset_closure (by simp)
  have hβB : β ∈ B := Subgroup.subset_closure (by simp)
  have hcomm : ({α, β} : Set (MulAut S)).Pairwise Commute := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hαβ
    · exact hαβ.symm
    · exact absurd rfl hxy
  letI : CommGroup B := Subgroup.closureCommGroupOfComm hcomm
  have hsq : ∀ b : B, b * b = 1 := by
    intro b
    have hb : b ∈ (⊤ : Subgroup B) := Subgroup.mem_top b
    rw [← Subgroup.closure_closure_coe_preimage (k := ({α, β} : Set (MulAut S)))] at hb
    refine Subgroup.closure_induction (p := fun b _ => b * b = 1) ?_ ?_ ?_ ?_ hb
    · intro x hx
      apply Subtype.ext
      change (x : MulAut S) * (x : MulAut S) = 1
      rcases hx with hx | hx
      · rw [hx, hα]
      · rw [hx, hβ]
    · simp
    · intro x y hx hy ihx ihy
      rw [mul_mul_mul_comm, ihx, ihy]
      simp
    · intro x hx ihx
      rw [inv_eq_of_mul_eq_one_left ihx, ihx]
  have hP : IsPGroup 2 B := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro b
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hsq b)
  let C : Subgroup (MulAut S ⧸ inner S) := B.map (QuotientGroup.mk' (inner S))
  have hC : IsCyclic C := hS B hP
  haveI : Fintype C := Fintype.ofFinite C
  let a : C := ⟨QuotientGroup.mk' (inner S) α, Subgroup.mem_map.mpr ⟨α, hαB, rfl⟩⟩
  let b : C := ⟨QuotientGroup.mk' (inner S) β, Subgroup.mem_map.mpr ⟨β, hβB, rfl⟩⟩
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    change (QuotientGroup.mk' (inner S) α) ^ 2 = 1
    rw [← map_pow, pow_two, hα, map_one]
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    change (QuotientGroup.mk' (inner S) β) ^ 2 = 1
    rw [← map_pow, pow_two, hβ, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hαo
    have hq : (QuotientGroup.mk' (inner S)) α = 1 := by
      have := congrArg (Subtype.val) h
      simpa [a] using this
    exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner S)
      α).mp hq
  have hb1 : b ≠ 1 := by
    intro h
    apply hβo
    have hq : (QuotientGroup.mk' (inner S)) β = 1 := by
      have := congrArg (Subtype.val) h
      simpa [b] using this
    exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner S)
      β).mp hq
  by_cases hab : a = b
  · have hgoal : (QuotientGroup.mk' (inner S)) (α * β) = 1 := by
      have hcoe : (QuotientGroup.mk' (inner S)) (α * β) =
          ((a * b : C) : MulAut S ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner S) := by
        rw [map_mul]
        rfl
      have hab' : (a * b : C) = 1 := by
        rw [hab]
        simpa [pow_two] using hb2
      rw [hcoe, hab']
      rfl
    exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner S)
      (α * β)).mp hgoal
  · exfalso
    have hcard3 : ({1, a, b} : Finset C).card = 3 := by
      have h1not : (1 : C) ∉ ({a, b} : Finset C) := by simp [ha1.symm, hb1.symm]
      have hanot : a ∉ ({b} : Finset C) := by simp [hab]
      rw [show ({1, a, b} : Finset C) = insert 1 (insert a {b}) from rfl,
        Finset.card_insert_of_notMem h1not, Finset.card_insert_of_notMem hanot,
        Finset.card_singleton]
    have hsub : ({1, a, b} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hx with rfl | rfl | rfl
      · simp
      · exact ha2
      · exact hb2
    have hle := Finset.card_le_card hsub
    haveI : IsCyclic C := hC
    have hbound := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
    omega

end CFSG.LocalAnalysis.WeakClosure81

end
