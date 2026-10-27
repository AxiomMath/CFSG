module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinG
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKSyl
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKCoord
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBCrit
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBV
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

theorem mulVec_eq_self_of_fixesA {n m : ℕ} {g : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hg : FixesA m g) {a : Fin n → ZMod 2} (ha : ∀ b : Fin n, m ≤ b.val → a b = 0) :
    g.mulVec a = a := by
  have hsum : a = ∑ b : Fin n, (a b) • (Pi.single b (1 : ZMod 2) : Fin n → ZMod 2) := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hsum]
  conv_rhs => rw [hsum]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mulVec_smul]
  by_cases hb : b.val < m
  · rw [hg b hb]
  · have : a b = 0 := ha b (by omega)
    simp [this]

section Coord

variable {G : Type} [Group G] [Finite G] {T L I K : Subgroup G} {m n j : ℕ}
  {α : ↥K →* GL (Fin n) (ZMod 2)} {β : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2)}

theorem centralizes_V_of_fixesA (hbij : Function.Bijective β)
    (hequi : ∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
      Multiplicative.toAdd (β v) i =
        ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u) i))
    (hVc : ∀ v : ↥(uZero I K), (v : G) ∈ vV T L → ∀ (i : Fin j) (b : Fin n), m ≤ b.val →
      Multiplicative.toAdd (β v) i b = 0)
    (hVU : vV T L ≤ uZero I K)
    (hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K) {x : ↥K}
    (hfix : FixesA m ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) :
    ∀ v ∈ vV T L, (x : G) * v * (x : G)⁻¹ = v := by
  intro v hv
  set v₀ : ↥(uZero I K) := ⟨v, hVU hv⟩ with hv₀
  set v₁ : ↥(uZero I K) := ⟨(x : G) * v * (x : G)⁻¹, hKU x v (hVU hv)⟩ with hv₁
  have h : v₁ = v₀ := by
    apply hbij.1
    apply Multiplicative.toAdd.injective
    funext i
    rw [hequi x v₀ v₁ rfl i]
    exact mulVec_eq_self_of_fixesA hfix (hVc v₀ hv i)
  exact congrArg Subtype.val h

theorem presA_of_conj_mem
    (hequi : ∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
      Multiplicative.toAdd (β v) i =
        ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u) i))
    (hVc : ∀ v : ↥(uZero I K), (v : G) ∈ vV T L → ∀ (i : Fin j) (b : Fin n), m ≤ b.val →
      Multiplicative.toAdd (β v) i b = 0)
    (hV2 : ∀ a : Fin n, a.val < m → ∃ v : ↥(uZero I K), (v : G) ∈ vV T L ∧
      ∃ i : Fin j, Multiplicative.toAdd (β v) i = Pi.single a 1)
    (hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K) {x : ↥K}
    (hx : ∀ v ∈ vV T L, (x : G) * v * (x : G)⁻¹ ∈ vV T L) :
    PresA m ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  intro a b ha hb
  obtain ⟨v, hvV, i, hvi⟩ := hV2 a ha
  set v₁ : ↥(uZero I K) := ⟨(x : G) * v * (x : G)⁻¹, hKU x v v.2⟩ with hv₁
  have hv₁V : (v₁ : G) ∈ vV T L := hx v hvV
  have h := hequi x v v₁ rfl i
  rw [hvi] at h
  have h0 := hVc v₁ hv₁V i b hb
  rw [h] at h0
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h0

end Coord

theorem centralizer_V_le_pCoreOf {G : Type} [Group G] [Finite G] {T M L I H K : Subgroup G}
    {m k : ℕ} (c : Conf4212 G T M L I H K) (hk : 0 < k)
    (hsum : IsSumOfNaturalModules (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)
      ⁅reducedAggregate (L ⊔ T), L⁆ ⊥
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I))
      (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k)
    {l : G} (hl : l ∈ perfectCore (L ⊓ H)) (hcen : ∀ v ∈ vV T L, l * v * l⁻¹ = v) :
    l ∈ pCoreOf 2 (perfectCore (L ⊓ H)) := by
  obtain ⟨α, hαs, hαk, hA, hZ, β, hβs, hβk, hβe⟩ := hsum
  set a : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) := ⟨l, Subgroup.mem_sup_left hl⟩ with ha
  have hα1 : α a = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext r s
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single (⟨0, hk⟩ : Fin k)
      (Pi.single s (1 : ZMod 2) : Fin m → ZMod 2)))
    have hconj : (u : G) = (a : G) * (u : G) * (a : G)⁻¹ := (hcen u u.2).symm
    have h := hβe a u u hconj ⟨0, hk⟩
    rw [hu] at h
    simp only [moduleAct, if_neg Bool.false_ne_true, toAdd_ofAdd, Pi.single_eq_same] at h
    have h' := congrFun h r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h'.symm
  have hmem : a ∈ α.ker := MonoidHom.mem_ker.mpr hα1
  rw [hαk] at hmem
  have hlR : l ∈ pCoreOf 2 I := Subgroup.mem_subgroupOf.mp hmem
  have hRO : pCoreOf 2 I ≤ pCoreOf 2 (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) := by
    have := C48Pf.le_pCoreOf_conjClosure_sup c.hypC28
    rwa [conjClosure_perfectCore c] at this
  exact inf_pCoreOf_sup_le_pCoreOf c (Subgroup.mem_inf.mpr ⟨hl, hRO hlR⟩)

theorem nsbFiveThreeTau_holds (hN31 : NotC31)
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h31 : Lemma31)
    (h32 : Lemma32) :
    ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
      NoSumBigData G T M L Mm I H K m k → ∀ (n j : ℕ) (hnm : n = m + 2), m = 3 →
        ∀ (α : ↥K →* GL (Fin n) (ZMod 2))
          (β : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2)),
          Function.Surjective α → α.ker = CFSG.pCore 2 ↥K → Function.Bijective β →
          (∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
            Multiplicative.toAdd (β v) i =
              ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
                (Multiplicative.toAdd (β u) i)) →
          (∀ v : ↥(uZero I K), (v : G) ∈ vV T L → ∀ (i : Fin j) (b : Fin n), m ≤ b.val →
            Multiplicative.toAdd (β v) i b = 0) →
          (∀ a : Fin n, a.val < m → ∃ v : ↥(uZero I K), (v : G) ∈ vV T L ∧
            ∃ i : Fin j, Multiplicative.toAdd (β v) i = Pi.single a 1) →
          ∃ x : ↥K, (x : G) ∈ pCoreOf 2 I ∧
            lowerBlock2 hnm ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) ≠ 1 := by
  intro G _ _ T M L Mm I H K m k hd n j hnm hm α β hsurj hker hbij hequi hVc hV2
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨hHK, -⟩ := h32 G T M L Mm I H K m k hd
  have hVU := vV_le_uZero hN31 h22 h27 hd
  obtain ⟨hRlt, hRC⟩ := h31 G T M L Mm I H K m k hd
  have hIH : I ≤ H := hd.2.1.2
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  have hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K := fun x z hz =>
    (Subgroup.mem_normalizer_iff.mp (hnormU (Subgroup.mem_sup_left x.2)) z).mp hz
  obtain ⟨-, -, -, hm34, hmk, -, -, hsum⟩ := id hd
  have hk : 0 < k := by omega
  have hLHN : perfectCore (L ⊓ H) ≤ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    hc.LH_le_normalizer_V
  have hcc : conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) :=
    conjClosure_perfectCore hc
  have hsyl : IsSylowTwoOf (pCoreOf 2 I)
      (centralizerSection (H ⊓ M) (perfectCore (L ⊓ H)) (pCoreOf 2 (perfectCore (L ⊓ H)))) := by
    have h := hc.hypC28.sylow
    rwa [hcc] at h
  set CH := centralizerSection (H ⊓ M) (perfectCore (L ⊓ H)) (pCoreOf 2 (perfectCore (L ⊓ H)))
    with hCH
  set X : Subgroup G := CH ⊓ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) with hX
  have hRX : pCoreOf 2 I ≤ X := fun r hr =>
    ⟨hsyl.1 hr, Subgroup.centralizer_le_normalizer _ (hRC (hRlt.le hr))⟩
  have hRsyl : IsSylowTwoOf (pCoreOf 2 I) X :=
    ⟨hRX, hsyl.2.1, fun hd' => hsyl.2.2 (hd'.trans (Dvd.intro _
      (Subgroup.relIndex_mul_relIndex _ X CH hRX inf_le_left)))⟩
  have hXH : X ≤ H := fun x hx => (centralizerSection_le_left _ _ _ hx.1).1
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := fun x hx => hHK (hXH hx)
  set N : Subgroup G := K ⊓ X with hN
  have hXnorm : X ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXK hx, Subgroup.le_normalizer hx⟩
  have hNsyl : IsSylowTwoOf (pCoreOf 2 I ⊓ N) N :=
    A4.isSylowTwoOf_inf_normal hRsyl inf_le_right hXnorm
  have hTop : IsSylowTwoOf ((pCoreOf 2 I ⊓ N).subgroupOf N) ⊤ :=
    CFSG.AGLEmbedding.isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hNsyl
  have hPres : ∀ y : ↥N,
      PresA m ((α ⟨y, (Subgroup.mem_inf.mp y.2).1⟩ : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) := by
    intro y
    refine presA_of_conj_mem hequi hVc hV2 hKU (x := ⟨y, (Subgroup.mem_inf.mp y.2).1⟩) ?_
    intro v hv
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp y.2).2).2
      v).mp hv
  let Λ : ↥N →* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
    { toFun := fun y => lowerBlock2 hnm ((α ⟨y, (Subgroup.mem_inf.mp y.2).1⟩ : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))
      map_one' := by
        have h1 : (⟨((1 : ↥N) : G), (Subgroup.mem_inf.mp (1 : ↥N).2).1⟩ : ↥K) = 1 := rfl
        show lowerBlock2 hnm ((α ⟨((1 : ↥N) : G), _⟩ : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) = 1
        rw [h1, map_one, Units.val_one, lowerBlock2_one hnm]
      map_mul' := by
        intro y y'
        have h1 : (⟨((y * y' : ↥N) : G), (Subgroup.mem_inf.mp (y * y' : ↥N).2).1⟩ : ↥K) =
            ⟨y, (Subgroup.mem_inf.mp y.2).1⟩ * ⟨y', (Subgroup.mem_inf.mp y'.2).1⟩ := rfl
        show lowerBlock2 hnm ((α ⟨((y * y' : ↥N) : G), _⟩ : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) = _
        rw [h1, map_mul, Units.val_mul, lowerBlock2_mul_of_presA hnm (hPres y) (hPres y')] }
  obtain ⟨gT, hgF, hgτ1, hgτ2⟩ := exists_gl_lower_transvection hnm
  obtain ⟨x₁, hx₁⟩ := hsurj gT
  have hx₁fix : FixesA m ((α x₁ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [hx₁]
    exact hgF
  have hx₁cen := centralizes_V_of_fixesA hbij hequi hVc hVU hKU hx₁fix
  have hx₁C : (x₁ : G) ∈ Subgroup.centralizer ((vV T L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (mul_inv_eq_iff_eq_mul.mp (hx₁cen v hv)).symm
  have hx₁V : (x₁ : G) ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hx₁C
  have hx₁H : (x₁ : G) ∈ H := le_of_mem_cComp hc.K_mem x₁.2
  have hx₁M : (x₁ : G) ∈ H ⊓ M := hc.hypC28.V_norm ⟨hx₁H, hx₁V⟩
  have hx₁L : (x₁ : G) ∈ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) := hc.LH_normal hx₁M
  have hx₁CH : (x₁ : G) ∈ CH := by
    refine mem_centralizerSection.mpr ⟨hx₁M, hx₁L,
      normalizer_le_normalizer_pCoreOf 2 (perfectCore (L ⊓ H)) hx₁L, fun l hl => ?_⟩
    have hlN : l ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) := hLHN hl
    have hlinv : ∀ w ∈ vV T L, l⁻¹ * w * l ∈ vV T L := by
      intro w hw
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) w).mp hw
      simpa using this
    apply centralizer_V_le_pCoreOf hc hk hsum (l := l * (x₁ : G) * l⁻¹ * (x₁ : G)⁻¹)
    · have h3 : (x₁ : G) * l⁻¹ * (x₁ : G)⁻¹ ∈ perfectCore (L ⊓ H) :=
        (Subgroup.mem_normalizer_iff.mp hx₁L l⁻¹).mp (Subgroup.inv_mem _ hl)
      have : l * (x₁ : G) * l⁻¹ * (x₁ : G)⁻¹ = l * ((x₁ : G) * l⁻¹ * (x₁ : G)⁻¹) := by
        simp only [mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ hl h3
    · intro v hv
      have e1 : (x₁ : G)⁻¹ * v * (x₁ : G) = v := by
        have hcomm : v * (x₁ : G) = (x₁ : G) * v := Subgroup.mem_centralizer_iff.mp hx₁C v hv
        calc (x₁ : G)⁻¹ * v * (x₁ : G) = (x₁ : G)⁻¹ * (v * (x₁ : G)) := by group
          _ = (x₁ : G)⁻¹ * ((x₁ : G) * v) := by rw [hcomm]
          _ = v := by group
      have e2 : (x₁ : G) * (l⁻¹ * v * l) * (x₁ : G)⁻¹ = l⁻¹ * v * l := hx₁cen _ (hlinv v hv)
      calc l * (x₁ : G) * l⁻¹ * (x₁ : G)⁻¹ * v * (l * (x₁ : G) * l⁻¹ * (x₁ : G)⁻¹)⁻¹
          = l * (x₁ : G) * l⁻¹ * ((x₁ : G)⁻¹ * v * (x₁ : G)) * l * (x₁ : G)⁻¹ * l⁻¹ := by group
        _ = l * ((x₁ : G) * (l⁻¹ * v * l) * (x₁ : G)⁻¹) * l⁻¹ := by rw [e1]; group
        _ = v := by rw [e2]; group
  have hx₁N : (x₁ : G) ∈ N := Subgroup.mem_inf.mpr ⟨x₁.2, hx₁CH, hx₁V⟩
  set x₀ : ↥N := ⟨x₁, hx₁N⟩ with hx₀
  have hΛx₀ : Λ x₀ = lowerBlock2 hnm ((gT : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) := by
    show lowerBlock2 hnm ((α x₁ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = _
    rw [hx₁]
  obtain ⟨t, ht, hne⟩ := exists_mem_ne_one_of_isSylowTwoOf hTop Λ.toHomUnits (x₀ := x₀)
    (Units.ext (by
      show (Λ x₀) ^ 2 = 1
      rw [pow_two, hΛx₀]
      exact hgτ2))
    (fun h => hgτ1 (by
      have := congrArg Units.val h
      simpa [hΛx₀] using this))
  have htN : (t : G) ∈ pCoreOf 2 I ⊓ N := Subgroup.mem_subgroupOf.mp ht
  refine ⟨⟨t, (Subgroup.mem_inf.mp t.2).1⟩, (Subgroup.mem_inf.mp htN).1, fun h => hne ?_⟩
  apply Units.ext
  show Λ t = 1
  exact h

end CFSG.Quasithin.H13.Ch4.NSB
