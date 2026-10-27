module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.Quasithin.H13.L32A74
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem conjClosure_le_centerOf (S : Setting147 G T L V (hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) {l₀ : G} (hl₀ : l₀ ∈ L) (hne : conjSub l₀ (fsuU T V) ≠ fsuU T V)
    {E : Subgroup G} (hEU : E ≤ fsuU T V)
    (hEN : ∀ m ∈ L, m ∈ Subgroup.normalizer (fsuU T V : Set G) →
      m ∈ Subgroup.normalizer (E : Set G))
    (hE : ∀ x ∈ E, ∀ y ∈ conjSub l₀ (fsuU T V), x * y = y * x) :
    conjClosure E L ≤ centerOf (sL T L V) := by
  have hES : ∀ e ∈ E, e ∈ Subgroup.centralizer (sL T L V : Set G) := by
    intro e he
    show e ∈ Subgroup.centralizer ((Subgroup.closure _ : Subgroup G) : Set G)
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, u, hu, rfl⟩
    by_cases hkU : conjSub k (fsuU T V) = fsuU T V
    · have hx : k * u * k⁻¹ ∈ fsuU T V := by rw [← hkU]; exact mul_mem_conjSub hu
      exact fsuU_comm S.hyp hx (hEU he)
    · obtain ⟨m, hm, hm1, hm2⟩ := lemma14_7_12_one S hF h13322 hMod (one_mem L) hl₀
        (one_mem L) hk (by rw [conjSub_one]; exact Ne.symm hne)
        (by rw [conjSub_one]; exact Ne.symm hkU)
      rw [mul_one, conjSub_one] at hm1
      have hmU : m ∈ Subgroup.normalizer (fsuU T V : Set G) := conjSub_eq_self_iff.mp hm1
      have hmE := hEN m hm hmU
      have hx : k * u * k⁻¹ ∈ conjSub m (conjSub l₀ (fsuU T V)) := by
        rw [← conjSub_mul, hm2]
        exact mul_mem_conjSub hu
      rw [mem_conjSub] at hx
      have he' : m⁻¹ * e * m ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hmE) e).mp he
        simpa using this
      have h1 := hE _ he' _ hx
      calc k * u * k⁻¹ * e = m * ((m⁻¹ * (k * u * k⁻¹) * m) * (m⁻¹ * e * m)) * m⁻¹ := by
            group
        _ = m * ((m⁻¹ * e * m) * (m⁻¹ * (k * u * k⁻¹) * m)) * m⁻¹ := by rw [h1]
        _ = e * (k * u * k⁻¹) := by group
  refine conjClosure_le fun l hl e he => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact mem_conjClosure hl (hEU he)
  · have hlS : l ∈ Subgroup.normalizer (sL T L V : Set G) := le_normalizer_conjClosure _ _ hl
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : l⁻¹ * s * l ∈ sL T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hlS) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hES e he) _ hs'
    calc s * (l * e * l⁻¹) = l * ((l⁻¹ * s * l) * e) * l⁻¹ := by group
      _ = l * (e * (l⁻¹ * s * l)) * l⁻¹ := by rw [h1]
      _ = l * e * l⁻¹ * s := by group

omit [Finite G] in
theorem comm_mem_of_two_step {X A Y : Subgroup G} {y : G} {m : ℕ} (hm : Odd m) (hym : y ^ m = 1)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hYA : Y ≤ A) (hAX : A ≤ X)
    (hyY : y ∈ Subgroup.normalizer (Y : Set G)) (hsq : ∀ a ∈ A, a ^ 2 ∈ Y)
    (hXA : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ A) (hAY : ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ Y)
    {x : G} (hx : x ∈ X) : y * x * y⁻¹ * x⁻¹ ∈ Y := by
  set a := y * x * y⁻¹ * x⁻¹ with ha
  have haA : a ∈ A := hXA x hx
  have hyaA : y * a * y⁻¹ ∈ A := by
    have := mul_mem (hYA (hAY a haA)) haA
    rwa [show y * a * y⁻¹ * a⁻¹ * a = y * a * y⁻¹ by group] at this
  set b' := y * a * y⁻¹ * a⁻¹ with hb'
  have hb'Y : b' ∈ Y := hAY a haA
  have hyx : y * x * y⁻¹ ∈ X := by
    have := mul_mem (hAX haA) hx
    rwa [show y * x * y⁻¹ * x⁻¹ * x = y * x * y⁻¹ by group] at this
  have key : ∀ k : ℕ, ∃ b ∈ Y, y ^ k * x * (y ^ k)⁻¹ * x⁻¹ = a ^ k * b := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, by group⟩
    | succ k ih =>
      obtain ⟨b, hb, hk⟩ := ih
      refine ⟨b' ^ k * (y * b * y⁻¹), mul_mem (pow_mem hb'Y k)
        ((Subgroup.mem_normalizer_iff.mp hyY b).mp hb), ?_⟩
      have hyaa : y * a * y⁻¹ = a * b' := by
        rw [hb']
        have := hXc _ (hAX hyaA) _ (hAX haA)
        calc y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
          _ = a * (y * a * y⁻¹ * a⁻¹) := by
            rw [hXc _ (hAX (hYA hb'Y)) _ (hAX haA)]
      have hpow : (y * a * y⁻¹) ^ k = a ^ k * b' ^ k := by
        rw [hyaa]
        exact (Commute.mul_pow (hXc _ (hAX haA) _ (hAX (hYA hb'Y))) k)
      have e1 : y ^ (k + 1) * x * (y ^ (k + 1))⁻¹ * x⁻¹ =
          y * (y ^ k * x * (y ^ k)⁻¹ * x⁻¹) * y⁻¹ * a := by
        rw [ha, pow_succ']
        group
      rw [e1, hk, show y * (a ^ k * b) * y⁻¹ = (y * a * y⁻¹) ^ k * (y * b * y⁻¹) by
        rw [conj_pow]; group, hpow]
      have hbY : y * b * y⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hyY b).mp hb
      have hc1 := hXc _ (hAX (hYA hbY)) _ (hAX haA)
      have hc2 := hXc _ (hAX (hYA (pow_mem hb'Y k))) _ (hAX haA)
      calc a ^ k * b' ^ k * (y * b * y⁻¹) * a = a ^ k * (b' ^ k * ((y * b * y⁻¹) * a)) := by
            group
        _ = a ^ k * (b' ^ k * (a * (y * b * y⁻¹))) := by rw [hc1]
        _ = a ^ k * ((b' ^ k * a) * (y * b * y⁻¹)) := by group
        _ = a ^ k * ((a * b' ^ k) * (y * b * y⁻¹)) := by rw [hc2]
        _ = a ^ (k + 1) * (b' ^ k * (y * b * y⁻¹)) := by rw [pow_succ]; group
  obtain ⟨b, hb, hk⟩ := key m
  rw [hym] at hk
  have ham : a ^ m ∈ Y := by
    have : a ^ m = b⁻¹ := by
      have e : (1 : G) * x * (1 : G)⁻¹ * x⁻¹ = 1 := by group
      rw [e] at hk
      exact eq_inv_of_mul_eq_one_left hk.symm
    rw [this]
    exact inv_mem hb
  obtain ⟨j, rfl⟩ := hm
  have e : a = a ^ (2 * j + 1) * ((a ^ 2) ^ j)⁻¹ := by
    rw [← pow_mul, pow_succ', mul_inv_cancel_right]
  rw [e]
  exact mul_mem ham (inv_mem (pow_mem (hsq a haA) j))

theorem normal_eq_of_not_mem_centralizer (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {N : Subgroup G} (hNL : N ≤ L) (hN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) {x : G}
    (hxN : x ∈ N) (hxV : x ∉ Subgroup.centralizer (V : Set G)) : N = L := by
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  have h1281 := h.hyp1281One h13322 hMod
  obtain ⟨hcard, hsq, hcomm⟩ := h1281.card_sq
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S14.LV
  set θ := repV hLV e with hθ
  have hθs : Function.Surjective θ := repV_surjective hLV e (autOn_eq_top_of_hyp1281One h1281)
  have hθk : θ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := repV_ker hLV e
  have hNn : (N.subgroupOf L).Normal := ⟨fun n hn l => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN l l.2 n hn⟩
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 le_rfl
  have himg : (N.subgroupOf L).map θ = ⊤ := by
    have hnorm : ((N.subgroupOf L).map θ).Normal := hNn.map θ hθs
    rcases hnorm.eq_bot_or_eq_top with hb | ht
    · exfalso
      apply hxV
      have h1 : θ ⟨x, hNL hxN⟩ = 1 := by
        rw [← Subgroup.mem_bot, ← hb]
        exact ⟨⟨x, hNL hxN⟩, Subgroup.mem_subgroupOf.mpr hxN, rfl⟩
      have h2 : (⟨x, hNL hxN⟩ : ↥L) ∈ θ.ker := h1
      rw [hθk, Subgroup.mem_subgroupOf] at h2
      exact h2
    · exact ht
  have h2 : ∀ y ∈ L, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
    intro y hy
    obtain ⟨n, hn, hny⟩ : θ ⟨y, hy⟩ ∈ (N.subgroupOf L).map θ := by
      rw [himg]; exact Subgroup.mem_top _
    have hc : n⁻¹ * ⟨y, hy⟩ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hny, inv_mul_cancel]
    rw [hθk, Subgroup.mem_subgroupOf] at hc
    have hcLT : ((n⁻¹ * ⟨y, hy⟩ : ↥L) : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (n⁻¹ * ⟨y, hy⟩).2, hc⟩
    obtain ⟨k, hk⟩ := S14.isPGroup_cent_sup ⟨_, hcLT⟩
    refine ⟨k, ?_⟩
    have hk' : ((n⁻¹ * ⟨y, hy⟩ : ↥L)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have hq : (QuotientGroup.mk (⟨y, hy⟩ ^ 2 ^ k) : ↥L ⧸ N.subgroupOf L) = 1 := by
      have e1 : (QuotientGroup.mk ⟨y, hy⟩ : ↥L ⧸ N.subgroupOf L) =
          QuotientGroup.mk (n⁻¹ * ⟨y, hy⟩) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          (QuotientGroup.eq_one_iff n).mpr hn, inv_one, one_mul]
      rw [QuotientGroup.mk_pow, e1, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    simpa using hq
  exact h.fsu.faithful.2.1 N hNL hNn h2

end CFSG.Quasithin.H13.L32A
