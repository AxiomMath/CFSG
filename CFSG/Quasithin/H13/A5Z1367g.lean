module

public import CFSG.Quasithin.H13.A5Z1367f
public import CFSG.Quasithin.H13.A5Z1367a
public import CFSG.Quasithin.H13.A5Z1367c
public import CFSG.Quasithin.H13.A5Z1367e

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

@[expose] def FactSylowNormS5 : Prop :=
  ∀ P : Subgroup (Equiv.Perm (Fin 5)), IsPGroup 2 P → ¬ 2 ∣ P.index →
    ∀ x ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 5))), orderOf x ≠ 3

@[expose] def FactSylowNormSL3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (m : ℕ), Odd m → Nat.card F = 2 ^ m →
    ∀ P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F), IsPGroup 2 P → ¬ 2 ∣ P.index →
      ∀ x ∈ Subgroup.normalizer (P : Set ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        orderOf x ≠ 3

@[expose] def SwapL21367 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) →
    S.GoodComp (autOn K S.Uv) → ∀ t ∈ S.Tv,
    autOn (K.map (MulAut.conj t).toMonoidHom) S.Uv ≠ autOn K S.Uv →
    ∀ G₁ G₂ : Subgroup (MulAut ↥S.Uv), G₁ ⊔ G₂ = S.JGv → G₁ ⊓ G₂ = ⊥ →
      (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) → autOn K S.Uv ≤ G₁ →
      autOn (K.map (MulAut.conj t).toMonoidHom) S.Uv ≤ G₂ →
      ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ n → Nat.card F = 2 ^ n →
        Nonempty (↥G₁ ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F)) → False

theorem false_of_sylowNorm {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ P : Subgroup Y, IsPGroup 2 P → ¬ 2 ∣ P.index →
      ∀ x ∈ Subgroup.normalizer (P : Set Y), orderOf x ≠ 3)
    {P : Subgroup X} (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) {g : X}
    (hg : g ∈ Subgroup.normalizer (P : Set X)) (hg3 : orderOf g = 3) : False := by
  refine hY (P.map e.toMonoidHom) (hP.map _) ?_ (e g) (Subgroup.le_normalizer_map _ ⟨g, hg, rfl⟩)
    (by rw [MulEquiv.orderOf_eq]; exact hg3)
  rw [show P.map e.toMonoidHom = P.map (e : X →* Y) from rfl, Subgroup.index_map_equiv]
  exact hidx

theorem false_of_sylowNorm_sub {V : Type} [CommGroup V] [Finite V] {G₁ S₁ : Subgroup (MulAut V)}
    {Y : Type} [Group Y] (e : ↥G₁ ≃* Y)
    (hY : ∀ P : Subgroup Y, IsPGroup 2 P → ¬ 2 ∣ P.index →
      ∀ x ∈ Subgroup.normalizer (P : Set Y), orderOf x ≠ 3)
    (hS₁ : IsSylowTwoOf S₁ G₁) {g : MulAut V} (hgG : g ∈ G₁)
    (hg : g ∈ Subgroup.normalizer (S₁ : Set (MulAut V))) (hg3 : orderOf g = 3) : False := by
  have hP : IsPGroup 2 ↥(S₁.subgroupOf G₁) :=
    hS₁.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₁.1).symm
  refine false_of_sylowNorm e hY hP hS₁.2.2 (g := ⟨g, hgG⟩) ?_ ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hg x
  · rw [← Subgroup.orderOf_coe]
    exact hg3

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem card_autOn_dvd (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) :
    Nat.card ↥(autOn K S.Uv) ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hKU : K ≤ Subgroup.normalizer (S.Uv : Set G) :=
    (le_of_mem_cComp hK).trans S.Gv_le_normalizer_Uv
  have hO2 : pCoreOf 2 (autOn K S.Uv) = ⊥ := by
    have hsub := A4.autOn_subnormal (V := S.Uv) (subnormal_of_mem_cComp hK)
    exact le_bot_iff.mp ((pCoreOf_two_le_of_subnormal hsub).trans
      (S.pCoreOf_GvS h1222 h517 hF).le)
  have hle := InternalSec.pCore_le_ker_autOnHom hKU hO2
  set f := QuotientGroup.lift (CFSG.pCore 2 ↥K) (InternalSec.autOnHom hKU) hle with hf
  have hsf : Function.Surjective f := by
    intro y
    obtain ⟨k, rfl⟩ := InternalSec.autOnHom_surjective hKU y
    exact ⟨QuotientGroup.mk k, QuotientGroup.lift_mk _ _ _⟩
  exact Subgroup.card_dvd_of_surjective (f := f) hsf

theorem Tv_le_normalizer_goodComp
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h56 : AsB56)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hS5 : FactSylowNormS5) (hSL3 : FactSylowNormSL3) (hSw : SwapL21367) (hH : S.Hyp1367)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hgood : S.GoodComp (autOn K S.Uv)) : S.Tv ≤ Subgroup.normalizer (K : Set G) := by
  have hF := hH.hF
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  have hq : CFSG.IsQuasisimple ↥(autOn K S.Uv) := B1Red.isQuasisimple_of_open hgood.1.2.2
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := le_of_mem_cComp hK
  have hKU : K ≤ Subgroup.normalizer (S.Uv : Set G) := hKG.trans S.Gv_le_normalizer_Uv
  refine S.Tv_le_normalizer_of_autOn h1222 h517 h37 hF hK hq ?_
  intro ts hts
  by_contra hN
  obtain ⟨⟨t, htN⟩, ht', rfl⟩ := Setup.mem_autOn_iff.1 hts
  have ht : t ∈ S.Tv := ht'
  have htG : t ∈ Subgroup.centralizer ({S.v12} : Set G) := S.Tv_le_Gv ht
  set ts := conjAct S.Uv ⟨t, htN⟩ with hts'
  set K₂ := K.map (MulAut.conj t).toMonoidHom with hK₂
  have hK₂eq : autOn K₂ S.Uv = B6.conjSub ts (autOn K S.Uv) :=
    autOn_map_conj hKU ⟨t, htN⟩
  have hne : autOn K₂ S.Uv ≠ autOn K S.Uv := fun h => hN (by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h' : B6.conjSub ts (autOn K S.Uv) = autOn K S.Uv := hK₂eq ▸ h
    exact h')
  have hgood₂ : S.GoodComp (autOn K₂ S.Uv) := hK₂eq ▸ S.isGoodComp_conj hgood hts
  have hJG := S.JGv_le_GvS
  have hc₁ : IsComponentOf (autOn K S.Uv) S.JGv :=
    isComponentOf_of_le hgood.1 (S.goodComp_le_JGv hgood) hJG
  have hc₂ : IsComponentOf (autOn K₂ S.Uv) S.JGv :=
    isComponentOf_of_le hgood₂.1 (S.goodComp_le_JGv hgood₂) hJG
  obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, hK₁, hK₂'⟩ :=
    two_components_cases hc₁ hc₂ hne.symm (S.b56Cases_JGv h1222 h517 h56 hF hH.hJ)
  have hG₁J : G₁ ≤ S.JGv := hsup ▸ le_sup_left
  have hG₂J : G₂ ≤ S.JGv := hsup ▸ le_sup_right
  obtain ⟨hC₁, hkind⟩ := factor_kind hf₁ (isComponentOf_of_le hc₁ hK₁ hG₁J)
  obtain ⟨hC₂, -⟩ := factor_kind hf₂ (isComponentOf_of_le hc₂ hK₂' hG₂J)
  rcases hkind with ⟨n, F, _, _, hn, hF2, he⟩ | hrest
  · exact hSw G T L V S hH K hK hgood t ht hne G₁ G₂ hsup hinf hc hK₁ hK₂' n F hn hF2 he
  have h3K : 3 ∣ Nat.card ↥(autOn K S.Uv) := by
    rcases hrest with ⟨-, h3⟩ | ⟨-, -, -, -, -, -, -, h3⟩
    · exact h3
    · exact h3
  have hnn : ¬ (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G))).Normal := by
    intro hn'
    apply hne
    have : K₂ = K := by
      rw [hK₂]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp hn' htG)
    rw [this]
  have hK₂K : K₂ ≠ K := fun h => hne (by rw [h])
  have hLv := S.LvS_le_sup h1222 h517 h37 h38 hF hK hnn
    ((S.card_autOn_dvd h1222 h517 hF hK) |> h3K.trans) htG hK₂K
  have hLJ : autOn S.Lv S.Uv ≤ S.JGv :=
    hLv.trans (sup_le (S.goodComp_le_JGv hgood) (S.goodComp_le_JGv hgood₂))
  have hsylJ := A4.isSylowTwoOf_inf_normal (S.isSylowTwoOf_TvS h1222 h517) hJG
    S.GvS_le_normalizer_JGv
  have hTL : ∀ s ∈ autOn S.Tv S.Uv,
      s ∈ Subgroup.normalizer ((autOn S.Lv S.Uv : Subgroup (MulAut ↥S.Uv)) :
        Set (MulAut ↥S.Uv)) := fun s hs =>
    B6.mem_normalizer_of_forall_mem (fun x hx => S.conj_mem_LvS hs hx) fun x hx => by
      have := S.conj_mem_LvS (Subgroup.inv_mem _ hs) hx
      rwa [inv_inv] at this
  have hTJ : ∀ s ∈ autOn S.Tv S.Uv,
      s ∈ Subgroup.normalizer ((autOn S.Tv S.Uv ⊓ S.JGv : Subgroup (MulAut ↥S.Uv)) :
        Set (MulAut ↥S.Uv)) := fun s hs => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) x),
      (Subgroup.mem_normalizer_iff.mp (S.GvS_le_normalizer_JGv (S.autOn_le_GvS S.Tv_le_Gv hs))
        x)]
  have hidxL : Nat.card ↥(autOn S.Lv S.Uv) ≤
      3 * Nat.card ↥(autOn S.Lv S.Uv ⊓ (autOn S.Tv S.Uv ⊓ S.JGv)) := by
    have h := S.card_LvS_le h1222 h517
    have e : autOn S.Lv S.Uv ⊓ (autOn S.Tv S.Uv ⊓ S.JGv) = autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv := by
      rw [inf_comm (autOn S.Tv S.Uv), ← inf_assoc, inf_eq_left.mpr hLJ]
    rw [e]
    exact h
  have hcent : ∀ {A B N : Subgroup (MulAut ↥S.Uv)}, A ⊔ B = S.JGv →
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → N ≤ B →
      B ⊓ Subgroup.centralizer (N : Set (MulAut ↥S.Uv)) = ⊥ →
      ∀ x ∈ S.JGv, (∀ n ∈ N, n * x = x * n) → x ∈ A := by
    intro A B N hAB hcAB hNB hCB x hx hxN
    obtain ⟨a, ha, b, hb, rfl⟩ := S153L.comp_exists_mul hcAB (hAB ▸ hx)
    have hb1 : b ∈ B ⊓ Subgroup.centralizer (N : Set (MulAut ↥S.Uv)) := by
      refine ⟨hb, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
      have h1 := hxN n hn
      have h2 := hcAB a ha n (hNB hn)
      have h3 : a * (n * b) = a * (b * n) := by
        calc a * (n * b) = (a * n) * b := by group
          _ = (n * a) * b := by rw [h2]
          _ = n * (a * b) := by group
          _ = a * b * n := h1
          _ = a * (b * n) := by group
      exact mul_left_cancel h3
    rw [hCB, Subgroup.mem_bot] at hb1
    rw [hb1, mul_one]
    exact ha
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hsup' : G₂ ⊔ G₁ = S.JGv := by rw [sup_comm]; exact hsup
  have htsG : ts ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
    S.autOn_le_GvS S.Tv_le_Gv hts
  have htsJ := S.GvS_le_normalizer_JGv htsG
  have hK₃ : B6.conjSub ts (autOn K₂ S.Uv) = autOn K S.Uv := by
    have hgood₃ := S.isGoodComp_conj hgood₂ hts
    have hc₃ : IsComponentOf (B6.conjSub ts (autOn K₂ S.Uv)) S.JGv :=
      isComponentOf_of_le hgood₃.1 (S.goodComp_le_JGv hgood₃) hJG
    rcases le_or_le_of_component hsup hc hc₃ with h | h
    · exact eq_of_components_le_factor hf₁ (isComponentOf_of_le hc₃ h hG₁J)
        (isComponentOf_of_le hc₁ hK₁ hG₁J)
    · exfalso
      have h1 := eq_of_components_le_factor hf₂ (isComponentOf_of_le hc₃ h hG₂J)
        (isComponentOf_of_le hc₂ hK₂' hG₂J)
      apply hne
      rw [hK₂eq] at h1 ⊢
      exact Subgroup.map_injective (MulAut.conj ts).injective h1
  have hmapG : G₁.map (MulAut.conj ts).toMonoidHom = G₂ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine hcent hsup' hc' hK₁ hC₁ _ ((Subgroup.mem_normalizer_iff.mp htsJ x).mp (hG₁J hx))
        fun n hn => ?_
      have hn' : n ∈ B6.conjSub ts (autOn K₂ S.Uv) := hK₃ ▸ hn
      obtain ⟨m, hm, rfl⟩ := hn'
      have h1 := hc x hx m (hK₂' hm)
      show ts * m * ts⁻¹ * (ts * x * ts⁻¹) = ts * x * ts⁻¹ * (ts * m * ts⁻¹)
      calc ts * m * ts⁻¹ * (ts * x * ts⁻¹) = ts * (m * x) * ts⁻¹ := by group
        _ = ts * (x * m) * ts⁻¹ := by rw [h1]
        _ = ts * x * ts⁻¹ * (ts * m * ts⁻¹) := by group
    · intro y hy
      have hx : ts⁻¹ * y * ts ∈ S.JGv := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htsJ) y).mp (hG₂J hy)
        rwa [inv_inv] at this
      have hxG₁ : ts⁻¹ * y * ts ∈ G₁ := by
        refine hcent hsup hc hK₂' hC₂ _ hx fun n hn => ?_
        have hn' : ts * n * ts⁻¹ ∈ autOn K S.Uv := hK₃ ▸ ⟨n, hn, rfl⟩
        have h1 := hc' y hy _ (hK₁ hn')
        calc n * (ts⁻¹ * y * ts) = ts⁻¹ * ((ts * n * ts⁻¹) * y) * ts := by group
          _ = ts⁻¹ * (y * (ts * n * ts⁻¹)) * ts := by rw [h1]
          _ = ts⁻¹ * y * ts * n := by group
      refine ⟨ts⁻¹ * y * ts, hxG₁, ?_⟩
      show ts * (ts⁻¹ * y * ts) * ts⁻¹ = y
      group
  obtain ⟨l, hl, hl3⟩ := S.exists_LvS_order_three
  obtain ⟨g, hg, hg3, hgN⟩ := exists_order_three_normalizer_of_swap hsup hinf hc hsylJ hLJ
    (fun s hs => hTL s hs.1) hidxL (hTJ ts hts) (hTL ts hts) hmapG hl hl3
  have hS₁ := A4.isSylowTwoOf_inf_normal hsylJ hG₁J (normal_left_of_commute hsup hc)
  rcases hrest with ⟨⟨e⟩, -⟩ | ⟨m, F, _, _, hm, hF, ⟨e⟩, -⟩
  · exact false_of_sylowNorm_sub e hS5 hS₁ hg hgN hg3
  · exact false_of_sylowNorm_sub e (hSL3 F m hm hF) hS₁ hg hgN hg3

end Setting

end CFSG.Quasithin.H13.A5
