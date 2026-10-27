module

public import CFSG.Quasithin.EmptyFaithful.S146D3
public import CFSG.Quasithin.EmptyFaithful.S146C7
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S146B4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Fixed

variable {G : Type} [Group G] {K Z U₁ U₂ : Subgroup G} {s : G}

theorem le_normalizer_conjSub {U : Subgroup G} (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) :
    K ≤ Subgroup.normalizer (conjSub s U : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_conjSub, mem_conjSub]
  have hk' : s⁻¹ * k * s ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsK) k).mp hk
    simpa using this
  have e : s⁻¹ * (k * x * k⁻¹) * s = (s⁻¹ * k * s) * (s⁻¹ * x * s) * (s⁻¹ * k * s)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (hKU hk') (s⁻¹ * x * s)

theorem le_normalizer_of_forall_commute {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    X ≤ Subgroup.normalizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have : x * z * x⁻¹ = z := by rw [h x hx z hz]; group
    rw [this]
    exact hz
  · intro hz
    have h1 := h x⁻¹ (X.inv_mem hx) _ hz
    have h3 : z = x * z * x⁻¹ := by
      have h4 : z * x⁻¹ = (x * z * x⁻¹) * x⁻¹ := by
        calc z * x⁻¹ = x⁻¹ * (x * z * x⁻¹) := by group
          _ = (x * z * x⁻¹) * x⁻¹ := h1
      exact mul_right_cancel h4
    rw [h3]
    exact hz

theorem Sec8.mem_of_fixed_conjSub (h : Sec8 K Z U₁) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hsZ : s ∈ Subgroup.normalizer (Z : Set G)) {u : G} (hu : u ∈ conjSub s U₁)
    (hfix : ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ Z) : u ∈ Z := by
  by_contra huZ
  have hu' : s⁻¹ * u * s ∈ U₁ := mem_conjSub.mp hu
  have hZ' : s⁻¹ * u * s ∉ Z := by
    intro hz
    apply huZ
    have := (Subgroup.mem_normalizer_iff.mp hsZ _).mp hz
    simpa [mul_assoc] using this
  obtain ⟨k, hk, hnc⟩ := h.exists_nc_of_not_mem hu' hZ'
  apply hnc
  have hk' : s * k * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hsK k).mp hk
  have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsZ) _).mp (hfix _ hk')
  have e : s⁻¹ * (u * (s * k * s⁻¹) * u⁻¹ * (s * k * s⁻¹)⁻¹) * s⁻¹⁻¹ =
      (s⁻¹ * u * s) * k * (s⁻¹ * u * s)⁻¹ * k⁻¹ := by group
  rw [e] at h2
  exact h2

theorem Sec8.mem_of_fixed_sup (h : Sec8 K Z U₁) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hsZ : s ∈ Subgroup.normalizer (Z : Set G)) (hU₂ : U₂ = conjSub s U₁) (hZU₂ : Z ≤ U₂)
    (hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set G))
    (hcomm : ∀ x ∈ U₁ ⊔ U₂, ∀ y ∈ U₁ ⊔ U₂, x * y = y * x) {y : G} (hy : y ∈ U₁ ⊔ U₂)
    (hfix : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ Z) : y ∈ Z := by
  have hKD : K ≤ Subgroup.normalizer ((U₁ ⊓ U₂ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨h.KU hk, hKU₂ hk⟩
  rcases h.irr (U₁ ⊓ U₂) (le_inf h.le hZU₂) inf_le_left hKD with hD | hD
  ·
    have hN : U₁ ≤ Subgroup.normalizer (U₂ : Set G) :=
      le_normalizer_of_forall_commute fun x hx z hz =>
        hcomm x (Subgroup.mem_sup_left hx) z (Subgroup.mem_sup_right hz)
    have hy' : y ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy'
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy'
    have hbk : ∀ k ∈ K, y₂ * k * y₂⁻¹ * k⁻¹ ∈ U₂ := by
      intro k hk
      have := (Subgroup.mem_normalizer_iff.mp (hKU₂ hk) y₂⁻¹).mp (U₂.inv_mem hy₂)
      have e : y₂ * k * y₂⁻¹ * k⁻¹ = y₂ * (k * y₂⁻¹ * k⁻¹) := by group
      rw [e]
      exact U₂.mul_mem hy₂ this
    have hak : ∀ k ∈ K, y₁ * k * y₁⁻¹ * k⁻¹ ∈ U₁ := by
      intro k hk
      have := (Subgroup.mem_normalizer_iff.mp (h.KU hk) y₁⁻¹).mp (U₁.inv_mem hy₁)
      have e : y₁ * k * y₁⁻¹ * k⁻¹ = y₁ * (k * y₁⁻¹ * k⁻¹) := by group
      rw [e]
      exact U₁.mul_mem hy₁ this
    have hcom : ∀ k ∈ K, (y₁ * y₂) * k * (y₁ * y₂)⁻¹ * k⁻¹ =
        (y₂ * k * y₂⁻¹ * k⁻¹) * (y₁ * k * y₁⁻¹ * k⁻¹) := by
      intro k hk
      have h1 : y₁ * (y₂ * k * y₂⁻¹ * k⁻¹) = (y₂ * k * y₂⁻¹ * k⁻¹) * y₁ :=
        hcomm y₁ (Subgroup.mem_sup_left hy₁) _ (Subgroup.mem_sup_right (hbk k hk))
      calc (y₁ * y₂) * k * (y₁ * y₂)⁻¹ * k⁻¹
          = (y₁ * (y₂ * k * y₂⁻¹ * k⁻¹)) * k * y₁⁻¹ * k⁻¹ := by group
        _ = ((y₂ * k * y₂⁻¹ * k⁻¹) * y₁) * k * y₁⁻¹ * k⁻¹ := by rw [h1]
        _ = (y₂ * k * y₂⁻¹ * k⁻¹) * (y₁ * k * y₁⁻¹ * k⁻¹) := by group
    have ha : ∀ k ∈ K, y₁ * k * y₁⁻¹ * k⁻¹ ∈ Z := by
      intro k hk
      have h2 := hfix k hk
      rw [hcom k hk] at h2
      have ha₂ : y₁ * k * y₁⁻¹ * k⁻¹ ∈ U₂ := by
        have e : y₁ * k * y₁⁻¹ * k⁻¹ =
            (y₂ * k * y₂⁻¹ * k⁻¹)⁻¹ * ((y₂ * k * y₂⁻¹ * k⁻¹) * (y₁ * k * y₁⁻¹ * k⁻¹)) := by group
        rw [e]
        exact U₂.mul_mem (U₂.inv_mem (hbk k hk)) (hZU₂ h2)
      rw [← hD]
      exact ⟨hak k hk, ha₂⟩
    have hy₁Z : y₁ ∈ Z := by
      by_contra hz
      obtain ⟨k, hk, hnc⟩ := h.exists_nc_of_not_mem hy₁ hz
      exact hnc (ha k hk)
    have hb : ∀ k ∈ K, y₂ * k * y₂⁻¹ * k⁻¹ ∈ Z := by
      intro k hk
      have h2 := hfix k hk
      rw [hcom k hk] at h2
      have e : y₂ * k * y₂⁻¹ * k⁻¹ =
          ((y₂ * k * y₂⁻¹ * k⁻¹) * (y₁ * k * y₁⁻¹ * k⁻¹)) * (y₁ * k * y₁⁻¹ * k⁻¹)⁻¹ := by group
      rw [e]
      exact Z.mul_mem h2 (Z.inv_mem (ha k hk))
    have hy₂' : y₂ ∈ conjSub s U₁ := by rw [← hU₂]; exact hy₂
    exact Z.mul_mem hy₁Z (h.mem_of_fixed_conjSub hsK hsZ hy₂' hb)
  ·
    have hle : U₁ ≤ U₂ := inf_eq_left.mp hD
    have hy2 : y ∈ conjSub s U₁ := by
      rw [← hU₂]
      rw [sup_eq_right.mpr hle] at hy
      exact hy
    exact h.mem_of_fixed_conjSub hsK hsZ hy2 hfix

end Fixed

section Decomp

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.sec8_of_decomp (S : Setting146 G T M) {K U₁ U₂ : Subgroup G} {s : G}
    (hK : K ∈ cComp (mcOf T)) (hL3 : KbarIsL3Two K) (hdec : IsDecompUK T M K U₁ U₂ s) :
    Sec8 K (quasithinOmegaOneCenter T) U₁ ∧ U₁ ≤ uOfL22 T M ∧ U₂ ≤ uOfL22 T M := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG
  have hUQ : conjClosure (VZ T M) (mcOf T) ≤ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf hG
  have hUN : conjClosure (VZ T M) (mcOf T) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := S.conjClosure_le_normalizer_Z hG
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) (mcOf T) :=
    Z_le_conjClosure_VZ T M (mcOf T)
  have hG₁U : mcOf T ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hG₁Z : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    S.normalizer_Z.ge hx
  have hKU : K ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) := hKG.trans hG₁U
  have hnat : mIdx U₁ (quasithinOmegaOneCenter T) = 3 ∧
      IsIrredOnSection K U₁ (quasithinOmegaOneCenter T) := by
    rcases hdec.natural with ⟨-, h3, hirr⟩ | ⟨h6', -⟩
    · exact ⟨h3, hirr⟩
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 h6').elim
  have hsup : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ⊔ quasithinOmegaOneCenter T = U₁ ⊔ U₂ := hdec.sup
  have hUU : U₁ ≤ conjClosure (VZ T M) (mcOf T) ∧ U₂ ≤ conjClosure (VZ T M) (mcOf T) := by
    have h1 : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ conjClosure (VZ T M) (mcOf T) :=
      S145.commutator_le_of_le_normalizer hKU
    have h2 : U₁ ⊔ U₂ ≤ conjClosure (VZ T M) (mcOf T) := by
      rw [← hsup]
      exact sup_le h1 hZU
    exact ⟨le_sup_left.trans h2, le_sup_right.trans h2⟩
  have hU₁2 : IsPGroup 2 U₁ := (pCoreOf_isPGroup 2 (mcOf T)).to_le (hUU.1.trans hUQ)
  refine ⟨{ le := hdec.Z₁
            norm := hUU.1.trans hUN
            sq := fun a ha => by
              rw [isElemAbelian_pow_eq_one hUab (hUU.1 ha)]
              exact Subgroup.one_mem _
            comm := fun a ha b hb => by
              have e : a * b * a⁻¹ * b⁻¹ = 1 := by
                rw [isElemAbelian_comm hUab (hUU.1 ha) (hUU.1 hb)]
                group
              rw [e]
              exact Subgroup.one_mem _
            card := by rw [HypF98.relIndex_eq_two_pow_mIdx hU₁2, hnat.1]; norm_num
            KZ := hKG.trans hG₁Z
            KU := hnat.2.2.1
            irr := hnat.2.2.2.2 }, hUU.1, hUU.2⟩

theorem cComp_cases (h37 : A37ForSQTK) (S : Setting146 G T M)
    (c21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K) {K : Subgroup G} (hK : K ∈ cComp (mcOf T)) :
    (∀ L ∈ cComp (mcOf T), L = K) ∨
      ∃ K' ∈ cComp (mcOf T), K' ≠ K ∧ (∀ L ∈ cComp (mcOf T), L = K ∨ L = K') ∧ KbarIsL3Two K := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hpc : pCoreOf 2 (mcOf T) ≠ ⊥ := hHTM.1.2
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hle : ∀ L ∈ cComp (mcOf T), L ≤ perfectCore (mcOf T) := fun L hL =>
    le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
  rcases c21 K hK with ⟨hper, -⟩ | ⟨⟨t, ht, htn, hper⟩, hL3⟩ | ⟨Kp, hKp, hKpK, -, -, hper, hL3, -⟩
  · exact Or.inl fun L hL => eq_of_le_cComp hK hL (hper ▸ hle L hL)
  · have hK' : conjSub t K ∈ cComp (mcOf T) := map_conj_mem_cComp hK (hTH ht)
    refine Or.inr ⟨conjSub t K, hK', fun heq => htn (A38.map_conj_eq_iff.mp heq),
      cComp_subset_pair S.hyp.qtke S.hyp.simple S.hyp.nonabelian h37 hpc hK hK' hper, hL3⟩
  · exact Or.inr ⟨Kp, hKp, hKpK, cComp_subset_pair S.hyp.qtke S.hyp.simple S.hyp.nonabelian h37 hpc
      hK hKp hper, hL3⟩

end Decomp

section Direct

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Nz" => Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)
local notation "Zz" => quasithinOmegaOneCenter T

theorem tilde_commutator_inf_eq_bot (S : Setting146 G T M) {K K' : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hL3 : KbarIsL3Two K) (hne : K' ≠ K) (c22 : Conc14622 T M K)
    (c22' : Conc14622 T M K') :
    tildeOf Zz ⁅uOfL22 T M, K⁆ ⊓ tildeOf Zz ⁅uOfL22 T M, K'⁆ = ⊥ := by
  obtain ⟨⟨U₁, U₂, s, hdec⟩, -⟩ := c22
  have hzero : ⁅⁅uOfL22 T M, K'⁆, K⁆ = ⊥ := c22'.2 K hK (Ne.symm hne)
  obtain ⟨hSec, hU₁, hU₂⟩ := S.sec8_of_decomp hK hL3 hdec
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hsT : s ∈ T := hdec.mem.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hdec.mem.2
  have hsZ : s ∈ Nz := by rw [S.normalizer_Z]; exact hTH hsT
  have hUel : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hHTM
  have hUN : uOfL22 T M ≤ Nz := S.conjClosure_le_normalizer_Z hHTM
  have hsup : ⁅uOfL22 T M, K⁆ ≤ U₁ ⊔ U₂ := by
    rw [← hdec.sup]
    exact le_sup_left
  have hcomm : ∀ x ∈ U₁ ⊔ U₂, ∀ y ∈ U₁ ⊔ U₂, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUel (sup_le hU₁ hU₂ hx) (sup_le hU₁ hU₂ hy)
  have hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set G) := by
    rw [hdec.conj]
    exact le_normalizer_conjSub hsK hSec.KU
  rw [eq_bot_iff]
  rintro w ⟨hw₁, hw₂⟩
  obtain ⟨a, ha, rfl⟩ := mem_secImg.mp hw₁
  obtain ⟨b, hb, hba⟩ := mem_secImg.mp hw₂
  have hab : (b : G)⁻¹ * a ∈ Zz := secMk_eq_secMk_iff.mp hba
  have hbK : ∀ k ∈ K, (b : G) * k * (b : G)⁻¹ * k⁻¹ = 1 := by
    intro k hk
    have h1 : ⁅(b : G), k⁆ ∈ ⁅⁅uOfL22 T M, K'⁆, K⁆ := Subgroup.commutator_mem_commutator hb hk
    rw [hzero] at h1
    simpa [commutatorElement_def] using h1
  have hfix : ∀ k ∈ K, (a : G) * k * (a : G)⁻¹ * k⁻¹ ∈ Zz := by
    intro k hk
    obtain ⟨z, hz, haz⟩ : ∃ z ∈ Zz, (a : G) = b * z := ⟨(b : G)⁻¹ * a, hab, by group⟩
    have hz' : k * z⁻¹ * k⁻¹ ∈ Zz :=
      (Subgroup.mem_normalizer_iff.mp (hSec.KZ hk) z⁻¹).mp (Subgroup.inv_mem _ hz)
    have e : (a : G) * k * (a : G)⁻¹ * k⁻¹ =
        (b : G) * (z * (k * z⁻¹ * k⁻¹)) * (b : G)⁻¹ * ((b : G) * k * (b : G)⁻¹ * k⁻¹) := by
      rw [haz]
      group
    rw [e, hbK k hk, mul_one]
    exact (Subgroup.mem_normalizer_iff.mp b.2 _).mp (Subgroup.mul_mem _ hz hz')
  have haZ : (a : G) ∈ Zz :=
    hSec.mem_of_fixed_sup hsK hsZ hdec.conj hdec.Z₂ hKU₂ hcomm (hsup ha) hfix
  exact Subgroup.mem_bot.mpr (secMk_eq_one_iff.mpr haZ)

theorem conc14623_three_direct (h37 : A37ForSQTK) (S : Setting146 G T M)
    (c21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K) (c22 : ∀ K ∈ cComp (mcOf T), Conc14622 T M K) :
    ∀ K ∈ cComp (mcOf T),
      tildeOf Zz ⁅uOfL22 T M, K⁆ ⊓
        (⨆ K' ∈ {K' | K' ∈ cComp (mcOf T) ∧ K' ≠ K}, tildeOf Zz ⁅uOfL22 T M, K'⁆) = ⊥ := by
  intro K hK
  rcases cComp_cases h37 S c21 hK with hsingle | ⟨K', hK', hne, hall, hL3⟩
  · have h0 : (⨆ K' ∈ {K' | K' ∈ cComp (mcOf T) ∧ K' ≠ K}, tildeOf Zz ⁅uOfL22 T M, K'⁆) = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun K'' hK'' => ?_)
      exact absurd (hsingle K'' hK''.1) hK''.2
    rw [h0, inf_bot_eq]
  · have hle : (⨆ K'' ∈ {K'' | K'' ∈ cComp (mcOf T) ∧ K'' ≠ K}, tildeOf Zz ⁅uOfL22 T M, K''⁆) ≤
        tildeOf Zz ⁅uOfL22 T M, K'⁆ := by
      refine iSup₂_le fun K'' hK'' => ?_
      rcases hall K'' hK''.1 with h | h
      · exact absurd h hK''.2
      · rw [h]
    exact le_bot_iff.mp ((inf_le_inf_left _ hle).trans
      (tilde_commutator_inf_eq_bot S hK hL3 hne (c22 K hK) (c22 K' hK')).le)

end Direct

end CFSG.Quasithin
