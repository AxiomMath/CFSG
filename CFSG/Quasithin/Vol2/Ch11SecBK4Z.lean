module

public import CFSG.Quasithin.Vol2.Ch11SecBK4Y
public import CFSG.Quasithin.Vol2.Ch11SecBFacts35
public import CFSG.Quasithin.Vol2.Ch11SecBK4T

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
open CFSG.Open (quasithinG2 quasithinZorn IsElemAbelian)
open scoped IsMulCommutative Pointwise

namespace BK4

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem hstep_stdF : ∀ i < 6, ∃ e ∈ G2Q8.stdF K (i + 1), e ∉ G2Q8.stdF K i ∧
    ∀ y ∈ G2Q8.stdF K (i + 1), ∃ c : K, y - c • e ∈ G2Q8.stdF K i := by
  intro i hi
  have hht : G2Q8.ht (G2Q8.bv i) = i := G2Q8.ht_bv hi
  refine ⟨Pi.single (G2Q8.bv i) 1, fun j hj => ?_, fun h => ?_, fun y hy =>
    ⟨y (G2Q8.bv i), fun j hj => ?_⟩⟩
  · have : j ≠ G2Q8.bv i := fun hjb => by rw [hjb, hht] at hj; omega
    simp [this]
  · have := (G2Q8.mem_stdF.mp h) (G2Q8.bv i) (by rw [hht])
    simp at this
  · by_cases hjb : j = G2Q8.bv i
    · subst hjb
      simp
    · have hj' : i + 1 ≤ G2Q8.ht j := by
        have : G2Q8.ht j ≠ i := fun h => hjb (G2Q8.eq_bv_of_ht h)
        omega
      simp [hjb, (G2Q8.mem_stdF.mp hy) j hj']

omit [CharP K 2] in
theorem stdF_top {i : ℕ} (hi : 6 ≤ i) : G2Q8.stdF K i = ⊤ :=
  eq_top_iff.mpr (G2Q8.stdF_six (F := K) ▸ G2Q8.stdF_mono hi)

theorem mapsTo_g2 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}
    (hf : KGNat.IsCoord (G2Q8.lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    {P : Subgroup (MulAut W)} {g : ↥(cayleyGroup K)} (hg : ∀ x : MulAut W, x ∈ P ↔
      ∃ u ∈ G2Q8.U0 K, x = ((G2Q8.rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {A : Subgroup (MulAut W)} (hAH : A ≤ H) (hPA : P ≤ A) (hA : Group.IsSolvable A)
    {a : MulAut W} (ha : a ∈ A) (i : ℕ) (w : W)
    (hw : f w ∈ G2Q8.gmapG g (G2Q8.stdF K i)) : f (a w) ∈ G2Q8.gmapG g (G2Q8.stdF K i) := by
  let φ : ↥(cayleyGroup K) →* MulAut W :=
    H.subtype.comp ((G2Q8.rhoG hc0 hc1 π).comp (MulAut.conj g).toMonoidHom)
  have hφ : ∀ b, φ b = ((G2Q8.rhoG hc0 hc1 π (g * b * g⁻¹) : ↥H) : MulAut W) := fun b => rfl
  have hφinj : Function.Injective φ := H.subtype_injective.comp
    ((G2Q8.rhoG_bijective hf hc0 hc1).1.comp (MulAut.conj g).injective)
  have hU : G2Q8.U0 K ≤ A.comap φ := by
    intro u hu
    rw [Subgroup.mem_comap, hφ]
    exact hPA ((hg _).mpr ⟨u, hu, rfl⟩)
  have hB : Group.IsSolvable ↥(A.comap φ) := by
    have := hA
    refine Group.isSolvable_of_isSolvable_injective (f := φ.subgroupComap A) fun x y h => ?_
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (hφinj h1)
  obtain ⟨b', hb'⟩ := (G2Q8.rhoG_bijective hf hc0 hc1).2 ⟨a, hAH ha⟩
  have hb : g⁻¹ * b' * g ∈ A.comap φ := by
    rw [Subgroup.mem_comap, hφ, show g * (g⁻¹ * b' * g) * g⁻¹ = b' by group, hb']
    exact ha
  have e1 : a w = ((G2Q8.rhoG hc0 hc1 π b' : ↥H) : MulAut W) w := by rw [hb']
  rw [e1, G2Q8.IsCoord.actG hf hc0 hc1, G2Q8.mem_gmapG,
    show b' = g * (g⁻¹ * b' * g) * g⁻¹ by group, G2Q8.conj_g2Act]
  have hw' := G2Q8.mem_gmapG.mp hw
  rcases Nat.lt_or_ge i 7 with hi | hi
  · exact (G2Q8.mem_stabQ.mp (le_stabQ_of_isSolvable hK hn hB hU (by omega) hb) _).mp hw'
  · rw [stdF_top (by omega)]
    exact Submodule.mem_top

variable {G : Type} [Group G] {L V T D : Subgroup G}

theorem cartanPower_g2 [Finite G] [IsMulCommutative ↥V] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)}
    (hf : KGNat.IsCoord (G2Q8.lmG K) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hDL : D ≤ L) (hD : IsElemAbelian p D) (hDT : (D : Set G) * T = T * D) {t : G}
    (ht : t ∈ T) (htD : t ∈ Subgroup.normalizer (D : Set G)) :
    ∃ r : ℕ, ∀ d ∈ D, t * d * t⁻¹ * (d ^ r)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g, hg⟩ := G2Q8.exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1
    (SecA.isSylowTwoOf_autOn hLV hTL')
  have hΨΦ : ∀ x, KGNat.zornLin ((g⁻¹ : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (KGNat.zornLin (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) x) = x := fun x => by
    rw [G2Q8.zornLin_apply_eq, G2Q8.zornLin_apply_eq, G2Q8.g2Act_inv_apply]
  have hΦΨ : ∀ x, KGNat.zornLin (g : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (KGNat.zornLin ((g⁻¹ : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) x) =
        x := fun x => by
    rw [G2Q8.zornLin_apply_eq, G2Q8.zornLin_apply_eq, G2Q8.g2Act_apply_inv]
  refine cartanPower_of_flag hf hLV (fun T hT => G2Q8.commutant_g2Derived hc0 hc1 _ T hT)
    (x₀ := q6 1 0 0 0 0 0) (fun h => by simpa [q6] using congrFun h (.inl 0))
    (fun x hxV hxL hx => mem_centralizer_of_g2 hLV hVL hf hc0 hc1 hxV hxL hx) hTS.2.1 hTV hTL
    (m := 6) (fun i => G2Q8.gmapG g (G2Q8.stdF K i)) ?_ ?_ (hstep_map _ _ hΨΦ hΦΨ hstep_stdF)
    ?_ ?_ ?_ hDL hp hp2 hD hDT ht htD
  · show G2Q8.gmapG g (G2Q8.stdF K 0) = ⊥
    rw [G2Q8.stdF_zero, G2Q8.gmapG, Submodule.map_bot]
  · intro i hi
    show G2Q8.gmapG g (G2Q8.stdF K i) = ⊤
    rw [stdF_top hi]
    exact eq_top_iff.mpr fun x _ => G2Q8.mem_gmapG.mpr Submodule.mem_top
  · intro i hi0 hi6
    exact G2Q8.isFlagW_preG hW hf hc0 hc1 hg (G2Q8.stdF_stable i) (G2Q8.card_stdF (by omega))
  · intro i hi0 hi6 U hU
    show U = hf.pre (G2Q8.gmapG g (G2Q8.stdF K i)).toAddSubgroup
    obtain ⟨S, hS, hcard, rfl⟩ := G2Q8.exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
    rw [G2Q8.eq_stdF_of_card hS hcard]
  · intro A hAH hPA hA a ha i w hw
    exact mapsTo_g2 hK hn hf hc0 hc1 hg hAH hPA hA ha i w hw

end BK4

theorem factCartanPower_holds : FactCartanPower := by
  intro G _ _ L V T D n p hV hn hLV hVL hnat hTS hTV hTL hp hp2 hDL hD hDT t ht htD
  obtain ⟨hc, hnat'⟩ := hnat
  rcases hnat' with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    exact BK4.cartanPower_sl3 hn hK hV hLV hVL hf hTS hTV hTL hp hp2 hDL hD hDT ht htD
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    exact BK4.cartanPower_sp4 hn hK hV hLV hVL hf hTS hTV hTL hp hp2 hDL hD hDT ht htD
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
    exact BK4.cartanPower_g2 hn hK hV hLV hVL hf hTS hTV hTL hp hp2 hDL hD hDT ht htD

end CFSG.Quasithin.Vol2.Ch11.SecB
