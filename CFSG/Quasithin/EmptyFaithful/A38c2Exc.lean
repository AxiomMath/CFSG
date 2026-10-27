module

public import CFSG.Quasithin.EmptyFaithful.A38c2Act
public import CFSG.Quasithin.EmptyFaithful.A38c2S3S3
public import CFSG.Quasithin.EmptyFaithful.A38cBasic
public import CFSG.Quasithin.EmptyFaithful.S153F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem no_s3s3_quotient_of_hom {X : Type*} [Group X] (f : X →* alternatingGroup (Fin 7))
    (φ : X →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (hφ : Function.Surjective φ)
    (hker : f.ker ≤ φ.ker) : False := by
  let ψ : ↥f.range →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    (QuotientGroup.lift f.ker φ hker).comp (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom
  refine a7_no_s3s3_quotient f.range ψ fun q => ?_
  obtain ⟨x, rfl⟩ := hφ q
  refine ⟨f.rangeRestrict x, ?_⟩
  have h : (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict x) = QuotientGroup.mk x := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp [ψ, h]

section Exc

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def tildeUActL (L : Subgroup G) : ↥L →* MulAut (tildeUL L) :=
  (tildeUAct L).comp (Subgroup.inclusion Subgroup.le_normalizer)

theorem tildeUActL_apply (l : ↥L) :
    tildeUActL L l = tildeUAct L ⟨(l : G), Subgroup.le_normalizer l.2⟩ := rfl

theorem ker_tildeUActL (hL : IsExcA7Block L) : (tildeUActL L).ker = CFSG.pCore 2 ↥L := by
  obtain ⟨hLsh, ⟨α, hα, hαk⟩, hidx⟩ := id hL
  have hle : CFSG.pCore 2 ↥L ≤ (tildeUActL L).ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    have hq' : ((q : ↥L) : G) ∈ blockQ L := by
      refine Subgroup.mem_map.mpr ⟨q, ?_, rfl⟩
      assumption
    exact tildeUAct_eq_one_of_mem_blockQ hLsh ⟨(q : G), Subgroup.le_normalizer q.2⟩ hq'
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have : (tildeUActL L).ker.Normal := MonoidHom.normal_ker _
  have : ((tildeUActL L).ker.map α).Normal := Subgroup.Normal.map inferInstance α hα
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((tildeUActL L).ker.map α) with h | h
  · refine le_antisymm (fun x hx => ?_) hle
    have hx' : α x ∈ (tildeUActL L).ker.map α := ⟨x, hx, rfl⟩
    rw [h] at hx'
    rw [← hαk]
    exact hx'
  · exfalso
    have htop : (tildeUActL L).ker = ⊤ := by
      rw [eq_top_iff]
      intro l _
      have hl : α l ∈ (tildeUActL L).ker.map α := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hml⟩ := hl
      have h1 : m⁻¹ * l ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hml, inv_mul_cancel]
      have h2 : m⁻¹ * l ∈ (tildeUActL L).ker := hle (hαk ▸ h1)
      have e : l = m * ((m⁻¹ * l)) := by group
      rw [e]
      exact Subgroup.mul_mem _ hm h2
    have hz : ∀ u ∈ blockU L, ∀ z ∈ blockZ L, u * z * u⁻¹ = z := fun u hu z hz => by
      have := Subgroup.mem_centralizer_iff.mp hz.2 u (blockU_le_block_self L hu)
      rw [this, mul_inv_cancel_right]
    obtain ⟨k, hk, u, hu, hnot⟩ := exists_nontrivial_conj_of_irr (K := L) (Z := blockZ L) (U := blockU L)
      inf_le_left
      (fun u hu => by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        refine ⟨fun hzZ => by rw [hz u hu z hzZ]; exact hzZ, fun hzZ => ?_⟩
        have h1 := hz u⁻¹ (inv_mem hu) _ hzZ
        have e : u⁻¹ * (u * z * u⁻¹) * u⁻¹⁻¹ = z := by group
        rw [e] at h1
        rw [h1]
        exact hzZ)
      (fun a ha => by
        rw [hLsh.2.2.1.2 a ha]
        exact Subgroup.one_mem _)
      hidx
      (Subgroup.le_normalizer.trans normalizerL_le_normalizer_blockZ)
      (fun W hZW hWU hLW => hLsh.2.2.2.2.2 W hZW hWU hLW)
    refine hnot (mem_blockZ_of_tildeUAct_eq_one (g := ⟨k, Subgroup.le_normalizer hk⟩) ?_ hu)
    have : (⟨k, hk⟩ : ↥L) ∈ (tildeUActL L).ker := by rw [htop]; exact Subgroup.mem_top _
    exact this

theorem card_range_tildeUActL (hL : IsExcA7Block L) : Nat.card (tildeUActL L).range = 2520 := by
  rw [← card_quotPCore_of_isExcA7Block hL]
  exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange (tildeUActL L)).symm.toEquiv.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_tildeUActL hL)).toEquiv)

theorem tildeUAct_conj_mem_range (n : ↥(Subgroup.normalizer (L : Set G))) {h : MulAut (tildeUL L)}
    (hh : h ∈ (tildeUActL L).range) : tildeUAct L n * h * (tildeUAct L n)⁻¹ ∈ (tildeUActL L).range := by
  obtain ⟨l, rfl⟩ := hh
  have hl : (n : G) * (l : G) * (n : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp n.2 l).mp l.2
  refine ⟨⟨(n : G) * l * (n : G)⁻¹, hl⟩, ?_⟩
  have e : (⟨(n : G) * l * (n : G)⁻¹, Subgroup.le_normalizer hl⟩ :
      ↥(Subgroup.normalizer (L : Set G))) = n * ⟨(l : G), Subgroup.le_normalizer l.2⟩ * n⁻¹ :=
    Subtype.ext rfl
  rw [tildeUActL_apply, tildeUActL_apply, e, map_mul, map_mul, map_inv]

theorem isPGroup_image_sup_mod_normalizer {S Y : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hYL : Y ≤ L) :
    IsPGroup 2 ↥(((Y ⊔ S).subgroupOf (Subgroup.normalizer (L : Set G))).map
      (QuotientGroup.mk' (L.subgroupOf (Subgroup.normalizer (L : Set G))))) := by
  have : (L.subgroupOf (Subgroup.normalizer (L : Set G))).Normal := Subgroup.normal_in_normalizer
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := hYL.trans Subgroup.le_normalizer
  have hS' : IsPGroup 2 ↥(S.subgroupOf (Subgroup.normalizer (L : Set G))) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  have hbot : (Y.subgroupOf (Subgroup.normalizer (L : Set G))).map
      (QuotientGroup.mk' (L.subgroupOf (Subgroup.normalizer (L : Set G)))) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact fun x hx => hYL hx
  rw [Subgroup.subgroupOf_sup hYN hSN, Subgroup.map_sup, hbot, bot_sup_eq]
  exact hS'.map _

theorem isPGroup_ker_tildeUAct_of_image [Finite G] (hL : IsExcA7Block L) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (L : Set G))
    (hX : IsPGroup 2 ↥((X.subgroupOf (Subgroup.normalizer (L : Set G))).map
      (QuotientGroup.mk' (L.subgroupOf (Subgroup.normalizer (L : Set G)))))) :
    IsPGroup 2 ↥((tildeUAct L).comp (Subgroup.inclusion hXN)).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (L.subgroupOf (Subgroup.normalizer (L : Set G))).Normal := Subgroup.normal_in_normalizer
  let K := ((tildeUAct L).comp (Subgroup.inclusion hXN)).ker
  let ψ : ↥K →* ↥(Subgroup.normalizer (L : Set G)) ⧸ L.subgroupOf (Subgroup.normalizer (L : Set G)) :=
    (QuotientGroup.mk' (L.subgroupOf (Subgroup.normalizer (L : Set G)))).comp
      ((Subgroup.inclusion hXN).comp K.subtype)
  have hxL : ∀ x : ↥ψ.ker, (((x : ↥K) : ↥X) : G) ∈ L := fun x => by
    have h1 : QuotientGroup.mk' (L.subgroupOf (Subgroup.normalizer (L : Set G)))
        (Subgroup.inclusion hXN ((x : ↥K) : ↥X)) = 1 := x.2
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion hXN ((x : ↥K) : ↥X))).mp h1)
  have hker : IsPGroup 2 ↥ψ.ker := by
    let κ : ↥ψ.ker →* ↥L :=
      MonoidHom.codRestrict (X.subtype.comp (K.subtype.comp ψ.ker.subtype)) L hxL
    have hκ : ∀ x, κ x ∈ CFSG.pCore 2 ↥L := fun x => by
      rw [← ker_tildeUActL hL, MonoidHom.mem_ker, tildeUActL_apply]
      exact (MonoidHom.mem_ker.mp (x : ↥K).2)
    let κ' : ↥ψ.ker →* ↥(CFSG.pCore 2 ↥L) := κ.codRestrict _ hκ
    refine IsPGroup.of_injective (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) κ' ?_
    intro x y hxy
    have h1 : ((κ x : ↥L) : G) = ((κ y : ↥L) : G) :=
      congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  have hrange : IsPGroup 2 ↥ψ.range := by
    refine hX.to_le ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion hXN k.1, Subgroup.mem_subgroupOf.mpr k.1.2, rfl⟩
  have hcomap := IsPGroup.comap_of_ker_isPGroup hrange ψ hker
  have htop : ψ.range.comap ψ = ⊤ := eq_top_iff.mpr fun x _ => ⟨x, rfl⟩
  rw [htop] at hcomap
  exact hcomap.of_equiv Subgroup.topEquiv

theorem excA7NoS3Section_holds : ExcA7NoS3Section := by
  intro G _ _ L S Y hL hS hSN hYL
  rintro ⟨φ, hφ, hker⟩
  obtain ⟨hΓ, hsimple⟩ := mulAut_tildeUL hL.1 hL.2.2
  have : IsSimpleGroup (MulAut (tildeUL L)) := hsimple
  have : Finite (MulAut (tildeUL L)) := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  obtain ⟨-, ⟨α, hα, hαk⟩, -⟩ := id hL
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := hYL.trans Subgroup.le_normalizer
  have hXN : Y ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le hYN hSN
  have hρN : ∀ n : ↥(Subgroup.normalizer (L : Set G)), tildeUAct L n ∈ (tildeUActL L).range := fun n => by
    refine mem_subgroup_of_mem_normalizer_card_2520 hΓ (card_range_tildeUActL hL) ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => tildeUAct_conj_mem_range n hh, fun hh => ?_⟩
    have h1 := tildeUAct_conj_mem_range n⁻¹ hh
    rw [map_inv, inv_inv] at h1
    have e : (tildeUAct L n)⁻¹ * (tildeUAct L n * h * (tildeUAct L n)⁻¹) * tildeUAct L n = h := by group
    rwa [e] at h1
  let ρH : ↥(Subgroup.normalizer (L : Set G)) →* ↥(tildeUActL L).range :=
    (tildeUAct L).codRestrict (tildeUActL L).range hρN
  let θ : ↥(tildeUActL L).range ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientKerEquivRange (tildeUActL L)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq ((ker_tildeUActL hL).trans hαk.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα))
  let f : ↥(Y ⊔ S) →* alternatingGroup (Fin 7) :=
    θ.toMonoidHom.comp (ρH.comp (Subgroup.inclusion hXN))
  have hK : IsPGroup 2 ↥((tildeUAct L).comp (Subgroup.inclusion hXN)).ker :=
    isPGroup_ker_tildeUAct_of_image hL hXN (isPGroup_image_sup_mod_normalizer hS hSN hYL)
  have hKle : ((tildeUAct L).comp (Subgroup.inclusion hXN)).ker ≤ CFSG.Open.pCore 2 ↥(Y ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hK
  refine no_s3s3_quotient_of_hom f φ hφ fun x hx => ?_
  have h1 : ρH (Subgroup.inclusion hXN x) = 1 := θ.map_eq_one_iff.mp hx
  have h2 : x ∈ ((tildeUAct L).comp (Subgroup.inclusion hXN)).ker := congrArg Subtype.val h1
  have h3 : x ∈ CFSG.Open.pCore 2 ↥(Y ⊔ S) := hKle h2
  rw [hker, Subgroup.mem_subgroupOf]
  refine Subgroup.mem_map.mpr ⟨x, Subgroup.mem_comap.mpr ?_, rfl⟩
  have h4 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(Y ⊔ S)) x = 1 := (QuotientGroup.eq_one_iff x).mpr h3
  rw [h4]
  exact Subgroup.one_mem _

end Exc

end CFSG.Quasithin
