module

public import CFSG.Quasithin.Background.A1bGroups
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.A1b

variable {G : Type*} [Group G]

namespace A1b

theorem conj_mem_centralizer_of_mem_normalizer {S : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
  have key := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * s := by group

theorem pow_eq_one_of_mem_closure_of_comm {S : Set G} {n : ℕ} (hS : ∀ x ∈ S, x ^ n = 1)
    (hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x)
    {x : G} (hx : x ∈ Subgroup.closure S) : x ^ n = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow n
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (hc x hx y hy) n, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

end A1b

section A111

variable [Finite G]

theorem twoReducedProduct_le_of_isSylowIn {K H T : Subgroup G} (hT : IsSylowIn 2 T K)
    (hF : K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K) (hTH : T ≤ H)
    (hHK : H ≤ K) : twoReducedProduct H ≤ twoReducedProduct K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine iSup₂_le fun V hV => ?_
  obtain ⟨hVH, hHV, hVel, hVred⟩ := hV
  have hVK : V ≤ K := hVH.trans hHK
  have hOK : pCoreOf 2 K ≤ T := pCoreOf_le_of_isSylowIn hT
  have hOKH : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hOK.trans hTH) (hHK.trans (le_normalizer_pCoreOf 2 K))
      (pCoreOf_isPGroup 2 K)
  have hOHC : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) := by
    refine hVred _ (pCoreOf_le 2 H) (le_normalizer_pCoreOf 2 H) ?_
    intro d hd
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [h1]
    exact Subgroup.one_mem _
  have hOKC : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) := hOKH.trans hOHC
  have hVC : V ≤ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact ((Subgroup.mem_centralizer_iff.1 (hOKC hc)) v hv).symm
  have hVO : V ≤ pCoreOf 2 K := fun v hv => hF ⟨hVK hv, hVC hv⟩
  set S := conjClosure V K with hS
  have hSK : S ≤ K := conjClosure_le fun h hh z hz =>
    K.mul_mem (K.mul_mem hh (hVK hz)) (K.inv_mem hh)
  have hSO : ∀ h ∈ K, ∀ z ∈ V, h * z * h⁻¹ ∈ pCoreOf 2 K ∧
      h * z * h⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    intro h hh z hz
    refine ⟨(Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 K hh) z).1 (hVO hz), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hc' : h⁻¹ * c * h ∈ pCoreOf 2 K := by
      have := (Subgroup.mem_normalizer_iff''.1 (le_normalizer_pCoreOf 2 K hh) c).1 hc
      exact this
    have := (Subgroup.mem_centralizer_iff.1 (hOKC hc')) z hz
    calc c * (h * z * h⁻¹) = h * ((h⁻¹ * c * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * c * h)) * h⁻¹ := by rw [this]
      _ = h * z * h⁻¹ * c := by group
  have hSO' : ∀ x ∈ S, x ∈ pCoreOf 2 K ∧ x ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    intro x hx
    have : S ≤ pCoreOf 2 K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) :=
      conjClosure_le fun h hh z hz => hSO h hh z hz
    exact this hx
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hSO' y hy).2 x (hSO' x hx).1
  have hSel : IsElemAbelian 2 S := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hScomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
    refine pow_eq_one_of_mem_closure_of_comm
      (S := {x | ∃ h ∈ K, ∃ z ∈ V, h * z * h⁻¹ = x}) (n := 2) ?_ hScomm hx
    rintro _ ⟨h, hh, z, hz, rfl⟩
    calc (h * z * h⁻¹) ^ 2 = h * z ^ 2 * h⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hVel.2 z hz]; group
  refine le_trans (le_conjClosure V K) (le_twoReducedProduct ⟨hSK, le_normalizer_conjClosure V K,
    hSel, ?_⟩)
  intro D hDK hKD hD
  have hCnorm : ∀ g ∈ K, ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := fun g hg c hc =>
    conj_mem_centralizer_of_mem_normalizer (le_normalizer_conjClosure V K hg) hc
  have hNn : ((D ⊓ Subgroup.centralizer (S : Set G)).subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨D.mul_mem (D.mul_mem g.2 hn.1) (D.inv_mem g.2), hCnorm g (hDK g.2) n hn.2⟩
  have hDsyl : IsSylowIn 2 (T ⊓ D) D :=
    hT.inf_normal hDK ((Subgroup.normal_subgroupOf_iff_le_normalizer hDK).2 hKD)
  have hq : ∀ x ∈ D, ∃ k : ℕ, x ^ 2 ^ k ∈ D ⊓ Subgroup.centralizer (S : Set G) := fun x hx => by
    obtain ⟨k, hk⟩ := hD x hx
    exact ⟨k, D.pow_mem hx _, hk⟩
  have hdec := exists_mul_eq_of_pow_mem hNn hq hDsyl
  have hSV : Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le (le_conjClosure V K)
  have hDH : D ⊓ H ≤ Subgroup.centralizer (V : Set G) := by
    refine hVred (D ⊓ H) inf_le_right ?_ ?_
    · intro h hh
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hKD (hHK hh), Subgroup.le_normalizer hh⟩
    · intro d hd
      obtain ⟨k, hk⟩ := hD d hd.1
      exact ⟨k, hSV hk⟩
  have hDV : D ≤ Subgroup.centralizer (V : Set G) := by
    intro d hd
    obtain ⟨s, hs, n, hn, rfl⟩ := hdec d hd
    exact Subgroup.mul_mem _ (hDH ⟨hs.2, hTH hs.1⟩) (hSV hn.2)
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : h⁻¹ * d * h ∈ D := (Subgroup.mem_normalizer_iff''.1 (hKD hh) d).1 hd
  have := Subgroup.mem_centralizer_iff.1 (hDV hd') z hz
  calc d * (h * z * h⁻¹) = h * ((h⁻¹ * d * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * d * h)) * h⁻¹ := by rw [this]
    _ = h * z * h⁻¹ * d := by group

end A111

section A119

variable [Finite G]

namespace A1b

omit [Finite G] in
theorem le_normalizer_centralizer {K D : Subgroup G}
    (hKD : K ≤ Subgroup.normalizer (D : Set G)) :
    K ≤ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => conj_mem_centralizer_of_mem_normalizer (hKD hg) hx
  · intro hx
    have := conj_mem_centralizer_of_mem_normalizer (hKD (K.inv_mem hg)) hx
    simpa [mul_assoc] using this

theorem centralizer_inf_centralizer_eq {K L U D : Subgroup G} (hLK : L ≤ K)
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hUel : IsElemAbelian 2 U) (hCU : L ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 L)
    (hDK : D ≤ K) (hKD : K ≤ Subgroup.normalizer (D : Set G))
    (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ Subgroup.centralizer (U : Set G)) :
    L ⊓ Subgroup.centralizer ((U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) =
      pCoreOf 2 L := by
  set C₀ := Subgroup.centralizer (U : Set G) with hC₀
  set U₁ : Subgroup G := U ⊓ Subgroup.centralizer (D : Set G) with hU₁
  have hLD : L ⊓ D ≤ C₀ := by
    have hp : IsPGroup 2 (L ⊓ D : Subgroup G) := by
      intro x
      obtain ⟨k, hk⟩ := hD x x.2.2
      have hxL : (x : G) ^ 2 ^ k ∈ L := L.pow_mem x.2.1 _
      have hmem : (x : G) ^ 2 ^ k ∈ pCoreOf 2 L := hCU ▸ ⟨hxL, hk⟩
      obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 L ⟨_, hmem⟩
      refine ⟨k + m, Subtype.ext ?_⟩
      have h1 : ((x : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      change (x : G) ^ 2 ^ (k + m) = 1
      rw [pow_add, pow_mul]
      exact h1
    have hn : L ≤ Subgroup.normalizer ((L ⊓ D : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hKD (hLK hg)⟩
    have := le_pCoreOf_of_le_normalizer 2 inf_le_left hn hp
    rw [← hCU] at this
    exact fun x hx => (this hx).2
  have hcomm : ∀ a ∈ L, ∀ b ∈ D, ∀ u ∈ U,
      a * b * u * (a * b)⁻¹ = b * a * u * (b * a)⁻¹ := by
    intro a ha b hb u hu
    have hc : a⁻¹ * b⁻¹ * a * b ∈ L ⊓ D := by
      refine ⟨?_, ?_⟩
      · have h1 : b⁻¹ * a * b ∈ L :=
          (Subgroup.mem_normalizer_iff''.1 (hKL (hDK hb)) a).1 ha
        have := L.mul_mem (L.inv_mem ha) h1
        simpa [mul_assoc] using this
      · have h1 : a⁻¹ * b⁻¹ * a ∈ D :=
          (Subgroup.mem_normalizer_iff''.1 (hKD (hLK ha)) b⁻¹).1 (D.inv_mem hb)
        exact D.mul_mem h1 hb
    have h2 := Subgroup.mem_centralizer_iff.1 (hLD hc) u hu
    have hcu : (a⁻¹ * b⁻¹ * a * b) * u * (a⁻¹ * b⁻¹ * a * b)⁻¹ = u := by
      rw [← h2]
      group
    calc a * b * u * (a * b)⁻¹
        = (b * a) * ((a⁻¹ * b⁻¹ * a * b) * u * (a⁻¹ * b⁻¹ * a * b)⁻¹) * (b * a)⁻¹ := by group
      _ = b * a * u * (b * a)⁻¹ := by rw [hcu]
  obtain ⟨B₀, hB₀, -⟩ := exists_isSylowIn_ge 2 (H := D) (P := ⊥) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  have hCnorm : ∀ g ∈ K, ∀ c ∈ C₀, g * c * g⁻¹ ∈ C₀ := fun g hg c hc =>
    conj_mem_centralizer_of_mem_normalizer (hKU hg) hc
  have hNn : ((D ⊓ C₀).subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨D.mul_mem (D.mul_mem g.2 hn.1) (D.inv_mem g.2), hCnorm g (hDK g.2) n hn.2⟩
  have hq : ∀ x ∈ D, ∃ k : ℕ, x ^ 2 ^ k ∈ D ⊓ C₀ := fun x hx => by
    obtain ⟨k, hk⟩ := hD x hx
    exact ⟨k, D.pow_mem hx _, hk⟩
  have hdec := exists_mul_eq_of_pow_mem hNn hq hB₀
  have hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKU hg, le_normalizer_centralizer hKD hg⟩
  have hKCU₁ : K ≤ Subgroup.normalizer (Subgroup.centralizer (U₁ : Set G) : Set G) :=
    le_normalizer_centralizer hKU₁
  apply le_antisymm
  · set K₀ := L ⊓ Subgroup.centralizer (U₁ : Set G) with hK₀
    have hK₀2 : IsPGroup 2 K₀ := by
      refine CFSG.SectionRank.Ccomm.isPGroup_of_coprime_eq_one (p := 2) fun a ha2 => ?_
      have haK₀ : (a : G) ∈ K₀ := a.2
      have haL : (a : G) ∈ L := haK₀.1
      have haK : (a : G) ∈ K := hLK haL
      have ha2' : (orderOf (a : G)).Coprime 2 := by rwa [← Subgroup.orderOf_coe a] at ha2
      have hU2 : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hUel.2 x x.2)⟩
      let ρ : K →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hKU)
      have hρ : ∀ (k : K) (u : U), ((ρ k u : U) : G) = (k : G) * u * (k : G)⁻¹ := fun k u => rfl
      have hB : IsPGroup 2 ((B₀.subgroupOf K).map ρ) :=
        (hB₀.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe (hB₀.le.trans hDK)).symm).map ρ
      have ha2'' : (orderOf (⟨(a : G), haK⟩ : K)).Coprime 2 := by
        rw [Subgroup.orderOf_mk]
        exact ha2'
      have key := thompson_AxB_element (p := 2) hU2 ρ hB (a := ⟨a, haK⟩) ha2'' ?_ ?_
      · have haC₀ : (a : G) ∈ C₀ := by
          rw [Subgroup.mem_centralizer_iff]
          intro u hu
          have h1 := congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : G)) key
          simp only [hρ, MulAut.one_apply] at h1
          rw [mul_inv_eq_iff_eq_mul] at h1
          exact h1.symm
        have haO : (a : G) ∈ pCoreOf 2 L := hCU ▸ ⟨haL, haC₀⟩
        obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 L ⟨_, haO⟩
        have h0 : (a : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
        have h1 : orderOf (a : G) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h0
        have h2 : orderOf (a : G) = 1 := Nat.Coprime.eq_one_of_dvd (ha2'.pow_right m) h1
        exact Subtype.ext (orderOf_eq_one_iff.1 h2)
      · intro b hb
        have hbD : (b : G) ∈ D := hB₀.le (Subgroup.mem_subgroupOf.1 hb)
        ext u
        simp only [MulAut.mul_apply, hρ]
        calc (a : G) * ((b : G) * u * (b : G)⁻¹) * (a : G)⁻¹
            = (a : G) * b * u * ((a : G) * b)⁻¹ := by group
          _ = (b : G) * a * u * ((b : G) * a)⁻¹ := hcomm a haL b hbD u u.2
          _ = (b : G) * ((a : G) * u * (a : G)⁻¹) * (b : G)⁻¹ := by group
      · intro x hx
        have hxC : (x : G) ∈ Subgroup.centralizer (D : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro d hd
          obtain ⟨s, hs, n, hn, rfl⟩ := hdec d hd
          have hsx : (s : G) * x * (s : G)⁻¹ = x := by
            have := hx ⟨s, hDK (hB₀.le hs)⟩ (Subgroup.mem_subgroupOf.2 hs)
            exact congrArg Subtype.val this
          have hnx : (x : G) * n = n * x := Subgroup.mem_centralizer_iff.1 hn.2 x x.2
          calc s * n * (x : G) = s * (n * x) := by group
            _ = s * (x * n) := by rw [hnx]
            _ = (s * x * s⁻¹) * (s * n) := by group
            _ = x * (s * n) := by rw [hsx]
        have hxU₁ : (x : G) ∈ U₁ := ⟨x.2, hxC⟩
        have hcx := Subgroup.mem_centralizer_iff.1 haK₀.2 x hxU₁
        apply Subtype.ext
        change (a : G) * x * (a : G)⁻¹ = x
        rw [← hcx]
        group
    have hn : L ≤ Subgroup.normalizer (K₀ : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hKCU₁ (hLK hg)⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hn hK₀2
  · rw [← hCU]
    exact inf_le_inf_left L (Subgroup.centralizer_le inf_le_left)

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (h : A ≤ B) (hB : IsElemAbelian p B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB h

end A1b

theorem centralizer_twoReducedProduct_eq {K L U : Subgroup G} (hLK : L ≤ K)
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) (hUK : U ≤ K)
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hUel : IsElemAbelian 2 U)
    (hCU : L ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 L) :
    L ⊓ Subgroup.centralizer (twoReducedProduct K : Set G) = pCoreOf 2 L := by
  obtain ⟨U₀, hU₀U, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun U' : Subgroup G => U' ≤ K ∧ K ≤ Subgroup.normalizer (U' : Set G) ∧
      IsElemAbelian 2 U' ∧ L ⊓ Subgroup.centralizer (U' : Set G) = pCoreOf 2 L) U
    ⟨hUK, hKU, hUel, hCU⟩
  obtain ⟨⟨hU₀K, hKU₀, hU₀el, hCU₀⟩, hmin'⟩ := hmin
  have hred : IsTwoReducedIn K U₀ := by
    refine ⟨hU₀K, hKU₀, hU₀el, fun D hDK hKD hD => ?_⟩
    have hcore := centralizer_inf_centralizer_eq hLK hKL hKU₀ hU₀el hCU₀ hDK hKD hD
    have hle : U₀ ⊓ Subgroup.centralizer (D : Set G) ≤ U₀ := inf_le_left
    have h1 := hmin' (y := U₀ ⊓ Subgroup.centralizer (D : Set G))
      ⟨hle.trans hU₀K, fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hKU₀ hg, le_normalizer_centralizer hKD hg⟩, isElemAbelian_of_le hle hU₀el, hcore⟩ hle
    exact Subgroup.le_centralizer_iff.1 (h1.trans inf_le_right)
  apply le_antisymm
  · rw [← hCU₀]
    exact inf_le_inf_left L (Subgroup.centralizer_le (le_twoReducedProduct hred))
  · intro x hx
    refine ⟨pCoreOf_le 2 L hx, ?_⟩
    have h1 : pCoreOf 2 L ≤ Subgroup.centralizer (twoReducedProduct K : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      refine iSup₂_le fun V hV => ?_
      rw [← Subgroup.le_centralizer_iff]
      obtain ⟨hVK, hKV, hVel, hVred⟩ := hV
      refine hVred _ ((pCoreOf_le 2 L).trans hLK)
        (hKL.trans (normalizer_le_normalizer_pCoreOf 2 L)) ?_
      intro d hd
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨d, hd⟩
      refine ⟨k, ?_⟩
      have h2 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [h2]
      exact Subgroup.one_mem _
    exact h1 hx

end A119

end CFSG.Quasithin
