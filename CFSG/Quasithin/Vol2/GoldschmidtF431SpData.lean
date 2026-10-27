module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLift
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLie

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252 CFSG.Open CFSG.Quasithin
  CFSG.Quasithin.F7 CFSG.LieType.BorelTits

universe u v

section Data

variable {D : Type} [Group D]

@[expose] def spZc (R : Fin 2 → Subgroup D) (j : Fin 2) : Subgroup D :=
  centerOf (perfectCore (Subgroup.normalizer (R j : Set D)))

structure SpDData (U : Subgroup D) (R : Fin 2 → Subgroup D) (i : Fin 3 → D) : Prop where
  borel : BorelData D U (R 0) (R 1)
  shape : SpShape U R
  Z_le : ∀ j, spZc R j ≤ centerOf U
  Z_ne : ∀ j, ∃ x ∈ spZc R j, x ≠ 1
  Z_trans : ∀ j, ∀ x ∈ spZc R j, ∀ y ∈ spZc R j, x ≠ 1 → y ≠ 1 →
    ∃ m ∈ Subgroup.normalizer (R j : Set D), m * x * m⁻¹ = y
  Z_inf : ∀ x, x ∈ spZc R 0 → x ∈ spZc R 1 → x = 1
  i_mem : ∀ k, i k ∈ centerOf U
  i_ne : ∀ k, i k ≠ 1
  i_sq : ∀ k, i k ^ 2 = 1
  i0 : i 0 ∈ spZc R 0
  i1 : i 1 ∈ spZc R 1
  i2 : i 2 ∉ spZc R 0 ∧ i 2 ∉ spZc R 1
  cent0 : pCoreOf 2 (Subgroup.centralizer ({i 0} : Set D)) = R 0
  cent1 : pCoreOf 2 (Subgroup.centralizer ({i 1} : Set D)) = R 1
  cent2 : Subgroup.centralizer ({i 2} : Set D) ≤ Subgroup.normalizer (U : Set D)
  fus : ∀ x ∈ U, x ≠ 1 → x ^ 2 = 1 →
    ∃ (k : Fin 3) (j : Fin 2), ∃ m ∈ Subgroup.normalizer (R j : Set D), m * x * m⁻¹ = i k

end Data

section Map

variable {D : Type*} {H : Type*} [Group D] [Group H] (Φ : D →* H)

theorem map_mem_normalizer_map {X : Subgroup D} {t : D}
    (ht : t ∈ Subgroup.normalizer (X : Set D)) :
    Φ t ∈ Subgroup.normalizer ((X.map Φ : Subgroup H) : Set H) := by
  have key : ∀ s ∈ Subgroup.normalizer (X : Set D), ∀ x ∈ X.map Φ,
      Φ s * x * (Φ s)⁻¹ ∈ X.map Φ := by
    intro s hs x hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨s * a * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs a).mp ha, by simp [map_mul]⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key t ht x
  · intro hx
    have := key t⁻¹ (inv_mem ht) _ hx
    have e : Φ t⁻¹ * (Φ t * x * (Φ t)⁻¹) * (Φ t⁻¹)⁻¹ = x := by
      rw [map_inv]
      group
    rwa [e] at this

theorem normalizer_map_inf_range (hΦ : Function.Injective Φ) (X : Subgroup D) :
    Subgroup.normalizer ((X.map Φ : Subgroup H) : Set H) ⊓ Φ.range =
      (Subgroup.normalizer (X : Set D)).map Φ := by
  ext g
  constructor
  · rintro ⟨hg, d, rfl⟩
    refine ⟨d, ?_, rfl⟩
    have hg' : Φ d ∈ Subgroup.normalizer ((X.map Φ : Subgroup H) : Set H) := hg
    show d ∈ Subgroup.normalizer (X : Set D)
    rw [Subgroup.mem_normalizer_iff] at hg' ⊢
    intro x
    have h := hg' (Φ x)
    rw [Subgroup.mem_map_iff_mem hΦ, show Φ d * Φ x * (Φ d)⁻¹ = Φ (d * x * d⁻¹) by simp [map_mul],
      Subgroup.mem_map_iff_mem hΦ] at h
    exact h
  · rintro ⟨t, ht, rfl⟩
    exact ⟨map_mem_normalizer_map Φ ht, t, rfl⟩

theorem centralizer_singleton_inf_range (hΦ : Function.Injective Φ) (a : D) :
    Subgroup.centralizer ({Φ a} : Set H) ⊓ Φ.range =
      (Subgroup.centralizer ({a} : Set D)).map Φ := by
  ext g
  constructor
  · rintro ⟨hg, d, rfl⟩
    refine ⟨d, ?_, rfl⟩
    have hg' : Φ d ∈ Subgroup.centralizer ({Φ a} : Set H) := hg
    show d ∈ Subgroup.centralizer ({a} : Set D)
    rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
    exact hΦ (by rw [map_mul, map_mul]; exact hg')
  · rintro ⟨c, hc, rfl⟩
    refine ⟨?_, c, rfl⟩
    have hc' : c ∈ Subgroup.centralizer ({a} : Set D) := hc
    show Φ c ∈ Subgroup.centralizer ({Φ a} : Set H)
    rw [Subgroup.mem_centralizer_singleton_iff] at hc' ⊢
    rw [← map_mul, ← map_mul, hc']

theorem centralizer_le_normalizer_of_pCoreOf [Finite H] (hΦ : Function.Injective Φ)
    [Φ.range.Normal] (a : D) {P : Subgroup D}
    (hP : pCoreOf 2 (Subgroup.centralizer ({a} : Set D)) = P) :
    Subgroup.centralizer ({Φ a} : Set H) ≤
      Subgroup.normalizer ((P.map Φ : Subgroup H) : Set H) := by
  set C : Subgroup H := Subgroup.centralizer ({Φ a} : Set H) with hC
  have h1 : C ⊓ Φ.range = (Subgroup.centralizer ({a} : Set D)).map Φ :=
    centralizer_singleton_inf_range Φ hΦ a
  have h2 : pCoreOf 2 (C ⊓ Φ.range) = P.map Φ := by
    rw [h1, pCoreOf_map_of_injective Φ hΦ, hP]
  calc C ≤ Subgroup.normalizer ((C ⊓ Φ.range : Subgroup H) : Set H) :=
        le_normalizer_inf_normal (Inn := Φ.range) C
    _ ≤ Subgroup.normalizer ((pCoreOf 2 (C ⊓ Φ.range) : Subgroup H) : Set H) :=
        normalizer_le_normalizer_pCoreOf 2 _
    _ = Subgroup.normalizer ((P.map Φ : Subgroup H) : Set H) := by rw [h2]

theorem SpShape.map (hΦ : Function.Injective Φ) {T : Subgroup D} {Q : Fin 2 → Subgroup D}
    (S : SpShape T Q) : SpShape (T.map Φ) (fun j => (Q j).map Φ) where
  Q_le j := Subgroup.map_mono (S.Q_le j)
  Q_norm j := by
    rintro _ ⟨t, ht, rfl⟩
    exact map_mem_normalizer_map Φ (S.Q_norm j ht)
  Q_abel j := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, S.Q_abel j a ha b hb]
  Z_le j := by
    rw [centerOf_map_of_injective Φ hΦ]
    exact Subgroup.map_mono (S.Z_le j)
  Z_sq := by
    intro z hz
    rw [centerOf_map_of_injective Φ hΦ] at hz
    obtain ⟨c, hc, rfl⟩ := hz
    rw [← map_pow, S.Z_sq c hc, map_one]
  inv_mem := by
    rintro _ ⟨t, ht, rfl⟩ h2
    have : t ^ 2 = 1 := hΦ (by rw [map_pow, h2, map_one])
    obtain ⟨j, hj⟩ := S.inv_mem t ht this
    exact ⟨j, Subgroup.mem_map_of_mem Φ hj⟩
  cen := by
    intro j x hx hxZ y hy hxy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have haZ : a ∉ centerOf T := fun h => hxZ (by
      rw [centerOf_map_of_injective Φ hΦ]
      exact Subgroup.mem_map_of_mem Φ h)
    have hab : b * a = a * b := hΦ (by rw [map_mul, map_mul]; exact hxy)
    exact Subgroup.mem_map_of_mem Φ (S.cen j a ha haZ b hb hab)
  ex := by
    intro j
    obtain ⟨a, ha, haZ, ha2⟩ := S.ex j
    refine ⟨Φ a, Subgroup.mem_map_of_mem Φ ha, ?_, by rw [← map_pow, ha2, map_one]⟩
    rw [centerOf_map_of_injective Φ hΦ]
    rintro ⟨c, hc, hca⟩
    exact haZ (hΦ hca ▸ hc)

end Map

theorem mem_normalizer_sup {G : Type*} [Group G] {A B : Subgroup G} {n : G}
    (hA : n ∈ Subgroup.normalizer (A : Set G)) (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ m : G, m ∈ Subgroup.normalizer (A : Set G) → m ∈ Subgroup.normalizer (B : Set G) →
      ∀ x ∈ A ⊔ B, m * x * m⁻¹ ∈ A ⊔ B := by
    intro m hmA hmB
    have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj m).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hmA x).mp hx)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hmB x).mp hx)
    intro x hx
    simpa [MulAut.conj_apply] using this hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key n hA hB x, fun hx => by simpa [mul_assoc] using key n⁻¹ (inv_mem hA) (inv_mem hB) _ hx⟩

section Lift

variable {D : Type} {H : Type u} [Group D] [Group H] [Finite D] [Finite H]

theorem exists_spLie_of_data (Φ : D →* H) (hΦ : Function.Injective Φ) [Φ.range.Normal]
    (hodd : Odd Φ.range.index) {U : Subgroup D} {R : Fin 2 → Subgroup D} {i : Fin 3 → D}
    (hD : SpDData U R i) (N : Fin 2 → Subgroup H)
    (hN : ∀ j, N j = Subgroup.normalizer ((R j).map Φ : Set H)) :
    ∃ (T : Subgroup H) (I : Finset H), F431SpLie T (N 0) (N 1) I := by
  classical
  set T : Subgroup H := U.map Φ with hT
  have hspN : ∀ j, spN (N 0) (N 1) j = N j := by
    intro j
    fin_cases j <;> rfl
  have hNinn : ∀ j, N j ⊓ Φ.range = (Subgroup.normalizer (R j : Set D)).map Φ := fun j => by
    rw [hN j]
    exact normalizer_map_inf_range Φ hΦ (R j)
  have hcore : ∀ j, pCoreOf 2 (Subgroup.normalizer (R j : Set D)) = R j := by
    intro j
    fin_cases j
    · exact hD.borel.core₁
    · exact hD.borel.core₂
  have hQ : ∀ j, spQ (N 0) (N 1) j = (R j).map Φ := fun j => by
    unfold spQ
    rw [hspN j, pCoreOf_eq_inf_of_odd (Inn := Φ.range) (N j) hodd, hNinn j,
      pCoreOf_map_of_injective Φ hΦ, hcore j]
  have hZ : ∀ j, spZ (N 0) (N 1) j = (spZc R j).map Φ := fun j => by
    unfold spZ spZc
    rw [hspN j, perfectCore_eq_inf_of_odd (Inn := Φ.range) (N j) hodd, hNinn j,
      perfectCore_map_of_injective Φ hΦ, centerOf_map_of_injective Φ hΦ]
  have SS : SpShape T (spQ (N 0) (N 1)) := by
    have h := hD.shape.map Φ hΦ
    have e : spQ (N 0) (N 1) = fun j => (R j).map Φ := funext hQ
    rw [e]
    exact h
  have hSyl : IsSylowTwoOf T ⊤ := isSylowTwoOf_map_of_odd Φ hΦ hodd hD.borel.sylow
  have hnormT : ∀ n, n ∈ Subgroup.normalizer (T : Set H) → ∀ j, n ∈ N j := by
    intro n hn j
    have h := SS.normalizer_le hSyl hn j
    rw [hQ j, ← hN j] at h
    exact h
  have hcenT : centerOf T = (centerOf U).map Φ := centerOf_map_of_injective Φ hΦ U
  have hZle : ∀ j, spZ (N 0) (N 1) j ≤ centerOf T := fun j => by
    rw [hZ j, hcenT]
    exact Subgroup.map_mono (hD.Z_le j)
  have hZcls : ∀ j, ∀ x ∈ spZ (N 0) (N 1) j, ∀ y ∈ centerOf T, IsConj x y →
      y ∈ spZ (N 0) (N 1) j := by
    intro j x hx y hy hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    obtain ⟨n, hn, hnx⟩ := exists_normalizer_conj_of_central hSyl (hZle j hx) hy hg
    have hnN : n ∈ spN (N 0) (N 1) j := by
      rw [hspN j]
      exact hnormT n hn j
    rw [← hnx]
    exact conj_mem_centerOf_perfectCore (M := spN (N 0) (N 1) j) hnN hx
  let I : Finset H := Finset.univ.image (fun k : Fin 3 => Φ (i k))
  have memI : ∀ k : Fin 3, Φ (i k) ∈ I := fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have memI' : ∀ x ∈ I, ∃ k : Fin 3, Φ (i k) = x := fun x hx => by
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hx
    exact ⟨k, hk⟩
  have hmem_map : ∀ (X : Subgroup D) (a : D), Φ a ∈ X.map Φ ↔ a ∈ X := fun X a =>
    Subgroup.mem_map_iff_mem hΦ
  have hiZ0 : Φ (i 0) ∈ spZ (N 0) (N 1) 0 := by
    rw [hZ 0]
    exact Subgroup.mem_map_of_mem Φ hD.i0
  have hiZ1 : Φ (i 1) ∈ spZ (N 0) (N 1) 1 := by
    rw [hZ 1]
    exact Subgroup.mem_map_of_mem Φ hD.i1
  have hi2Z0 : Φ (i 2) ∉ spZ (N 0) (N 1) 0 := by
    rw [hZ 0, hmem_map]
    exact hD.i2.1
  have hi2Z1 : Φ (i 2) ∉ spZ (N 0) (N 1) 1 := by
    rw [hZ 1, hmem_map]
    exact hD.i2.2
  have hi1Z0 : Φ (i 1) ∉ spZ (N 0) (N 1) 0 := by
    rw [hZ 0, hmem_map]
    intro h
    exact hD.i_ne 1 (hD.Z_inf _ h hD.i1)
  have hi0Z1 : Φ (i 0) ∉ spZ (N 0) (N 1) 1 := by
    rw [hZ 1, hmem_map]
    intro h
    exact hD.i_ne 0 (hD.Z_inf _ hD.i0 h)
  have hiT : ∀ k, Φ (i k) ∈ centerOf T := fun k => by
    rw [hcenT]
    exact Subgroup.mem_map_of_mem Φ (hD.i_mem k)
  have hnc : ∀ k k' : Fin 3, IsConj (Φ (i k)) (Φ (i k')) → k = k' := by
    intro k k' h
    by_contra hne
    fin_cases k <;> fin_cases k'
    · exact hne rfl
    · exact hi1Z0 (hZcls 0 _ hiZ0 _ (hiT 1) h)
    · exact hi2Z0 (hZcls 0 _ hiZ0 _ (hiT 2) h)
    · exact hi0Z1 (hZcls 1 _ hiZ1 _ (hiT 0) h)
    · exact hne rfl
    · exact hi2Z1 (hZcls 1 _ hiZ1 _ (hiT 2) h)
    · exact hi2Z0 (hZcls 0 _ hiZ0 _ (hiT 2) h.symm)
    · exact hi2Z1 (hZcls 1 _ hiZ1 _ (hiT 2) h.symm)
    · exact hne rfl
  have hcentU : pCoreOf 2 (Subgroup.centralizer ({i 2} : Set D)) = U := by
    have hUC : U ≤ Subgroup.centralizer ({i 2} : Set D) := fun u hu => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mem_centerOf_iff.mp (hD.i_mem 2)).2 u hu
    apply le_antisymm
    · exact isSylowTwoOf_pCoreOf_le (isSylowTwoOf_mono_right hD.borel.sylow hUC le_top)
    · exact le_pCoreOf_of_le_normalizer 2 hUC hD.cent2 hD.borel.sylow.2.1
  have hc0 : Subgroup.centralizer ({Φ (i 0)} : Set H) ≤ N 0 := by
    rw [hN 0]
    exact centralizer_le_normalizer_of_pCoreOf Φ hΦ (i 0) hD.cent0
  have hc1 : Subgroup.centralizer ({Φ (i 1)} : Set H) ≤ N 1 := by
    rw [hN 1]
    exact centralizer_le_normalizer_of_pCoreOf Φ hΦ (i 1) hD.cent1
  have hc2 : Subgroup.centralizer ({Φ (i 2)} : Set H) ≤ N 0 ⊓ N 1 := by
    intro g hg
    have := centralizer_le_normalizer_of_pCoreOf Φ hΦ (i 2) hcentU hg
    exact ⟨hnormT g this 0, hnormT g this 1⟩
  refine ⟨T, I, ?_⟩
  refine
    { W :=
        { sylow := hSyl
          T_le₁ := ?_
          T_le₂ := ?_
          mem_T := ?_
          order_two := ?_
          two_le := ?_
          rep := ?_
          fusion := ?_ }
      Q_abel := SS.Q_abel
      Z_le_Q := SS.Z_le
      Z_sq := SS.Z_sq
      inv_mem := SS.inv_mem
      cen := SS.cen
      ex := SS.ex
      O2N12 := ?_
      I_center := ?_
      I_type := ?_
      Z_le := hZle
      Z_cls := hZcls
      Z_trans := ?_
      Z_ne := ?_ }
  ·
    rintro _ ⟨u, hu, rfl⟩
    rw [hN 0]
    exact map_mem_normalizer_map Φ (hD.shape.Q_norm 0 hu)
  · rintro _ ⟨u, hu, rfl⟩
    rw [hN 1]
    exact map_mem_normalizer_map Φ (hD.shape.Q_norm 1 hu)
  · intro x hx
    obtain ⟨k, rfl⟩ := memI' x hx
    exact Subgroup.mem_map_of_mem Φ (mem_centerOf_iff.mp (hD.i_mem k)).1
  · intro x hx
    obtain ⟨k, rfl⟩ := memI' x hx
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hD.i_sq k, map_one]
    · intro h
      exact hD.i_ne k (hΦ (by rw [h, map_one]))
  · have hne : Φ (i 0) ≠ Φ (i 1) := fun h => hi0Z1 (by rw [h]; exact hiZ1)
    calc 2 = ({Φ (i 0), Φ (i 1)} : Finset H).card := (Finset.card_pair hne).symm
      _ ≤ I.card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact memI 0
        · exact memI 1)
  · intro x hx
    have hx2 : x ^ (2 ^ 1) = 1 := by
      rw [pow_one]
      exact hx ▸ pow_orderOf_eq_one x
    obtain ⟨d, rfl⟩ := mem_of_pow_two_pow_eq_one (Inn := Φ.range) hodd hx2
    have hd2 : orderOf d = 2 := by
      rw [← hx]
      exact (orderOf_injective Φ hΦ d).symm
    obtain ⟨m, -, hm⟩ := exists_conj_mem_of_isSylowTwoOf_involution hD.borel.sylow
      (Subgroup.mem_top d) hd2
    have hu1 : m⁻¹ * d * m ≠ 1 := by
      intro h
      have : d = 1 := by
        calc d = m * (m⁻¹ * d * m) * m⁻¹ := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at hd2
      exact absurd hd2 (by norm_num)
    have hu2 : (m⁻¹ * d * m) ^ 2 = 1 := by
      have : d ^ 2 = 1 := by rw [← hd2]; exact pow_orderOf_eq_one d
      calc (m⁻¹ * d * m) ^ 2 = m⁻¹ * d ^ 2 * m := by rw [sq, sq]; group
        _ = 1 := by rw [this]; group
    obtain ⟨k, j, p, -, hp⟩ := hD.fus _ hm hu1 hu2
    have hconj : IsConj (Φ (i k)) (Φ d) := by
      refine isConj_iff.mpr ⟨Φ (m * p⁻¹), ?_⟩
      have e : m * p⁻¹ * i k * (m * p⁻¹)⁻¹ = d := by rw [← hp]; group
      rw [← map_inv, ← map_mul, ← map_mul, e]
    refine ⟨Φ (i k), ⟨memI k, hconj⟩, ?_⟩
    rintro y ⟨hyI, hyc⟩
    obtain ⟨k', rfl⟩ := memI' y hyI
    rw [hnc k' k (hyc.trans hconj.symm)]
  · intro x hx hxo
    obtain ⟨u, hu, rfl⟩ := hx
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at hxo
      exact absurd hxo (by norm_num)
    have hu2 : u ^ 2 = 1 := hΦ (by
      rw [map_pow, map_one]
      exact hxo ▸ pow_orderOf_eq_one _)
    obtain ⟨k, j, m, hm, hmu⟩ := hD.fus u hu hu1 hu2
    refine ⟨Φ (i k), memI k, ?_⟩
    have hmN : Φ m ∈ N j := by
      rw [hN j]
      exact map_mem_normalizer_map Φ hm
    have e : Φ m * Φ u * (Φ m)⁻¹ = Φ (i k) := by
      rw [← map_inv, ← map_mul, ← map_mul, hmu]
    fin_cases j
    · exact Or.inl ⟨Φ m, hmN, e⟩
    · exact Or.inr ⟨Φ m, hmN, e⟩
  ·
    have hTle : T ≤ N 0 ⊓ N 1 := by
      refine le_inf ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        rw [hN 0]
        exact map_mem_normalizer_map Φ (hD.shape.Q_norm 0 hu)
      · rintro _ ⟨u, hu, rfl⟩
        rw [hN 1]
        exact map_mem_normalizer_map Φ (hD.shape.Q_norm 1 hu)
    have hTjoin : T = (R 0).map Φ ⊔ (R 1).map Φ := by
      rw [← Subgroup.map_sup, hD.borel.sup]
    apply le_antisymm
    · exact isSylowTwoOf_pCoreOf_le (isSylowTwoOf_mono_right hSyl hTle le_top)
    · have hnorm : N 0 ⊓ N 1 ≤ Subgroup.normalizer (T : Set H) := by
        intro n hn
        rw [hTjoin]
        refine mem_normalizer_sup ?_ ?_
        · have := hn.1
          rwa [hN 0] at this
        · have := hn.2
          rwa [hN 1] at this
      exact le_pCoreOf_of_le_normalizer 2 hTle hnorm (hSyl.2.1)
  · intro x hx
    obtain ⟨k, rfl⟩ := memI' x hx
    exact hiT k
  · intro x hx
    obtain ⟨k, rfl⟩ := memI' x hx
    fin_cases k
    · exact Or.inl ⟨hiZ0, hc0⟩
    · exact Or.inr (Or.inl ⟨hiZ1, hc1⟩)
    · exact Or.inr (Or.inr hc2)
  · intro j x hx y hy hx1 hy1
    rw [hZ j] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy1' : y' ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨m, hm, hmx⟩ := hD.Z_trans j x' hx' y' hy' hx1' hy1'
    refine ⟨Φ m, ?_, ?_⟩
    · rw [hspN j, hN j]
      exact map_mem_normalizer_map Φ hm
    · rw [← map_inv, ← map_mul, ← map_mul, hmx]
  · intro j
    obtain ⟨x, hx, hx1⟩ := hD.Z_ne j
    refine ⟨Φ x, ?_, fun h => hx1 (hΦ (by rw [h, map_one]))⟩
    rw [hZ j]
    exact Subgroup.mem_map_of_mem Φ hx

end Lift

end CFSG.Quasithin.H13.F431
