module

public import CFSG.Quasithin.Background.F918H0
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.Quasithin.Background.F918P2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Aux

theorem d321a_le_or_le {G : Type*} [Group G] {A B N : Subgroup G}
    (hA : ∀ x ∈ A ⊔ B, ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hB : ∀ x ∈ A ⊔ B, ∀ b ∈ B, x * b * x⁻¹ ∈ B)
    (hN : ∀ x ∈ A ⊔ B, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hNle : N ≤ A ⊔ B)
    (hNs : IsSimpleGroup ↥N) (hnab : ∃ n ∈ N, ∃ n' ∈ N, n * n' ≠ n' * n) :
    N ≤ A ∨ N ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hNA, hNB⟩ := hcon
  have key : ∀ C : Subgroup G, C ≤ A ⊔ B → (∀ x ∈ A ⊔ B, ∀ c ∈ C, x * c * x⁻¹ ∈ C) →
      ¬ N ≤ C → ∀ n ∈ N, ∀ c ∈ C, n * c = c * n := by
    intro C hCle hC hNC n hn c hc
    have : (C.subgroupOf N).Normal :=
      ⟨fun x hx g => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hC g (hNle g.2) x hx⟩
    rcases hNs.eq_bot_or_eq_top_of_normal (C.subgroupOf N) with h | h
    · have h1 : n * c * n⁻¹ * c⁻¹ ∈ C := C.mul_mem (hC n (hNle hn) c hc) (C.inv_mem hc)
      have h2 : n * c * n⁻¹ * c⁻¹ ∈ N := by
        have h3 := hN c (hCle hc) n⁻¹ (N.inv_mem hn)
        have e : n * c * n⁻¹ * c⁻¹ = n * (c * n⁻¹ * c⁻¹) := by group
        rw [e]
        exact N.mul_mem hn h3
      have h3 : (⟨n * c * n⁻¹ * c⁻¹, h2⟩ : ↥N) ∈ C.subgroupOf N := h1
      rw [h, Subgroup.mem_bot] at h3
      have h4 : n * c * n⁻¹ * c⁻¹ = 1 := congrArg Subtype.val h3
      calc n * c = (n * c * n⁻¹ * c⁻¹) * (c * n) := by group
        _ = c * n := by rw [h4, one_mul]
    · exfalso
      apply hNC
      intro n' hn'
      have : (⟨n', hn'⟩ : ↥N) ∈ C.subgroupOf N := by rw [h]; trivial
      exact this
  have hAc := key A le_sup_left hA hNA
  have hBc := key B le_sup_right hB hNB
  obtain ⟨n, hn, n', hn', hne⟩ := hnab
  apply hne
  have hcent : A ⊔ B ≤ Subgroup.centralizer ({n} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hAc h hn a ha
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hBc h hn b hb
  have := hcent (hNle hn')
  rw [Subgroup.mem_centralizer_iff] at this
  exact this n rfl

variable {W : Type} [CommGroup W]

theorem d321a_conjAutSub_mul (a b : MulAut W) (X : Subgroup (MulAut W)) :
    conjAutSub (a * b) X = conjAutSub a (conjAutSub b X) := by
  ext x
  simp only [mem_conjAutSub_iff]
  have e : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [e]

theorem d321a_conjAutSub_inj {a : MulAut W} {X Y : Subgroup (MulAut W)}
    (h : conjAutSub a X = conjAutSub a Y) : X = Y := by
  have := congrArg (conjAutSub a⁻¹) h
  rwa [conjAutSub_inv_conjAutSub, conjAutSub_inv_conjAutSub] at this

theorem d321a_mem_normalizer_iff {g : MulAut W} {X : Subgroup (MulAut W)} :
    g ∈ Subgroup.normalizer (X : Set (MulAut W)) ↔ conjAutSub g X = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem d321a_card_conjAutSub (g : MulAut W) (X : Subgroup (MulAut W)) :
    Nat.card ↥(conjAutSub g X) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem d321a_le_stabSub_of_inv {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : ∀ x ∈ X, ∀ w ∈ U, x w ∈ U) : X ≤ stabSub U := by
  intro x hx u
  refine ⟨fun hxu => ?_, h x hx u⟩
  have := h x⁻¹ (X.inv_mem hx) (x u) hxu
  simpa using this

theorem d321a_fixV_sup (X Y : Subgroup (MulAut W)) : fixV (X ⊔ Y) = fixV X ⊓ fixV Y :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq X Y

theorem d321a_commOf_eq_commSub (H : Subgroup (MulAut W)) (I : Subgroup W) :
    XMod.commOf ↥H I = commSub I H := by
  unfold XMod.commOf commSub
  congr 1
  ext c
  constructor
  · rintro ⟨a, l, hl, rfl⟩
    exact ⟨a, a.2, l, hl, rfl⟩
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨⟨x, hx⟩, w, hw, rfl⟩

theorem d321a_commV_stable {L : Subgroup (MulAut W)} {m : MulAut W}
    (hm : m ∈ Subgroup.normalizer (L : Set (MulAut W))) {u : W} (hu : u ∈ commV L) :
    m u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hm hu

def d321a_actTriv (V C : Subgroup W) : Subgroup (MulAut W) where
  carrier := {x | x ∈ stabSub V ∧ ∀ v ∈ V, x v * v⁻¹ ∈ C}
  one_mem' := ⟨(stabSub V).one_mem, fun v _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨(stabSub V).mul_mem hx1 hy1, fun v hv => ?_⟩
    have hyv : y v ∈ V := (mem_stabSub.mp hy1 v).2 hv
    have e : (x * y) v * v⁻¹ = (x (y v) * (y v)⁻¹) * (y v * v⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact C.mul_mem (hx2 _ hyv) (hy2 v hv)
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨(stabSub V).inv_mem hx1, fun v hv => ?_⟩
    have hxv : x⁻¹ v ∈ V := (mem_stabSub.mp ((stabSub V).inv_mem hx1) v).2 hv
    have e : x⁻¹ v * v⁻¹ = (x (x⁻¹ v) * (x⁻¹ v)⁻¹)⁻¹ := by
      simp
    rw [e]
    exact C.inv_mem (hx2 _ hxv)

theorem d321a_commSub_sup_le {V : Subgroup W} {X Y : Subgroup (MulAut W)}
    (h : X ⊔ Y ≤ stabSub V) : commSub V (X ⊔ Y) ≤ commSub V X ⊔ commSub V Y := by
  have hle : X ⊔ Y ≤ d321a_actTriv V (commSub V X ⊔ commSub V Y) := by
    refine sup_le (fun x hx => ⟨h (Subgroup.mem_sup_left hx), fun v hv => ?_⟩)
      (fun y hy => ⟨h (Subgroup.mem_sup_right hy), fun v hv => ?_⟩)
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨y, hy, v, hv, rfl⟩)
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  exact (hle hx).2 v hv

end Aux

section Helpers

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d321_comm_eq (hstd : D3Std M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L)
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) : commSub V L = V := by
  have hirr := hstd.hyp.irr
  have hinv : ∀ x ∈ Mp, ∀ w ∈ V, x w ∈ V := fun x hx w hw => hirr.2.1 ⟨x, hx⟩ w hw
  have hcomm : commSub V Mp = V := by
    rw [← d321a_commOf_eq_commSub]
    exact hirr.2.2.1
  have hstab : L ⊔ conjAutSub t L ≤ stabSub V := by
    rw [← hMp]
    exact d321a_le_stabSub_of_inv hinv
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hLt : commSub V (conjAutSub t L) = ⊥ :=
    commSub_eq_bot_iff.mpr (fun v hv g hg => htriv v hv g hg)
  apply le_antisymm
  · calc commSub V L ≤ commSub V Mp := commSub_mono le_rfl hLMp
      _ = V := hcomm
  · calc V = commSub V Mp := hcomm.symm
      _ = commSub V (L ⊔ conjAutSub t L) := by rw [hMp]
      _ ≤ commSub V L ⊔ commSub V (conjAutSub t L) := d321a_commSub_sup_le hstab
      _ = commSub V L := by rw [hLt, sup_bot_eq]

theorem d321a_perm (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hcomm : ⁅L, conjAutSub t L⁆ = ⊥) (hMp : Mp = L ⊔ conjAutSub t L)
    (hMpn : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) {g : MulAut W} (hg : g ∈ M) :
    conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L := by
  subst hMp
  have hLc : conjAutSub t L ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp ((Subgroup.commutator_comm _ _).trans hcomm)
  have hLc' : L ≤ Subgroup.centralizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hMpL : L ⊔ conjAutSub t L ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer (hLc.trans (Subgroup.centralizer_le_normalizer _))
  have hMpLt : L ⊔ conjAutSub t L ≤
      Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    sup_le (hLc'.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hA : ∀ x ∈ L ⊔ conjAutSub t L, ∀ a ∈ L, x * a * x⁻¹ ∈ L := fun x hx a ha =>
    (Subgroup.mem_normalizer_iff.mp (hMpL hx) a).mp ha
  have hB : ∀ x ∈ L ⊔ conjAutSub t L, ∀ b ∈ conjAutSub t L, x * b * x⁻¹ ∈ conjAutSub t L :=
    fun x hx b hb => (Subgroup.mem_normalizer_iff.mp (hMpLt hx) b).mp hb
  have hNle : conjAutSub g L ≤ L ⊔ conjAutSub t L := by
    intro n hn
    have h1 : g⁻¹ * n * g ∈ L := mem_conjAutSub_iff.mp hn
    have h2 := (Subgroup.mem_normalizer_iff.mp (hMpn hg) _).mp (Subgroup.mem_sup_left h1)
    have e : g * (g⁻¹ * n * g) * g⁻¹ = n := by group
    rwa [e] at h2
  have hNn : ∀ x ∈ L ⊔ conjAutSub t L, ∀ n ∈ conjAutSub g L, x * n * x⁻¹ ∈ conjAutSub g L := by
    intro x hx n hn
    rw [mem_conjAutSub_iff] at hn ⊢
    have hx' : g⁻¹ * x * g ∈ L ⊔ conjAutSub t L :=
      (Subgroup.mem_normalizer_iff''.mp (hMpn hg) x).mp hx
    have e : g⁻¹ * (x * n * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * n * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e]
    exact hA _ hx' _ hn
  have hNs : IsSimpleGroup ↥(conjAutSub g L) :=
    haveI := hLs
    (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.isSimpleGroup
  have hnab' : ∃ n ∈ conjAutSub g L, ∃ n' ∈ conjAutSub g L, n * n' ≠ n' * n := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨g * a * g⁻¹, mem_conjAutSub_iff.mpr ?_, g * b * g⁻¹, mem_conjAutSub_iff.mpr ?_,
      fun h => hab ?_⟩
    · have e : g⁻¹ * (g * (a : MulAut W) * g⁻¹) * g = a := by group
      rw [e]
      exact a.2
    · have e : g⁻¹ * (g * (b : MulAut W) * g⁻¹) * g = b := by group
      rw [e]
      exact b.2
    · apply Subtype.ext
      have h' : g * ((a : MulAut W) * b) * g⁻¹ = g * ((b : MulAut W) * a) * g⁻¹ := by
        calc g * ((a : MulAut W) * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
          _ = g * ((b : MulAut W) * a) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h')
  rcases d321a_le_or_le hA hB hNn hNle hNs hnab' with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (d321a_card_conjAutSub g L).ge)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h
      ((d321a_card_conjAutSub t L).trans (d321a_card_conjAutSub g L).symm).le)

omit [Finite W] in
theorem d321a_core
    (hgen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤) (hLM : L ≤ M) (htM : t ∈ M)
    (hperm : ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hVL : commSub V L = V) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
      commV L ≤ fixV (conjAutSub t L) := by
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hmemP : ∀ g : MulAut W, g ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ↔
      g ∈ M ∧ conjAutSub g L = L := fun g => by
    rw [Subgroup.mem_inf, d321a_mem_normalizer_iff]
  have hti : conjAutSub t⁻¹ L = conjAutSub t L := by
    rcases hperm t⁻¹ (M.inv_mem htM) with h | h
    · exfalso
      apply htL
      have h1 : t⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        d321a_mem_normalizer_iff.mpr h
      simpa using (Subgroup.normalizer (L : Set (MulAut W))).inv_mem h1
    · exact h
  have hPLt : ∀ m ∈ M, conjAutSub m L = L → conjAutSub m (conjAutSub t L) = conjAutSub t L := by
    intro m hm hmL
    rcases hperm (m * t) (M.mul_mem hm htM) with h | h
    · exfalso
      apply htL
      rw [d321a_conjAutSub_mul] at h
      exact d321a_mem_normalizer_iff.mpr (d321a_conjAutSub_inj (h.trans hmL.symm))
    · rwa [d321a_conjAutSub_mul] at h
  have hsplit : ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub (t⁻¹ * g) L = L := by
    intro g hg
    rcases hperm g hg with h | h
    · exact Or.inl h
    · right
      rw [d321a_conjAutSub_mul, h, conjAutSub_inv_conjAutSub]
  obtain ⟨U₀, hU0mem, hU0le⟩ : ∃ U₀ : Subgroup W,
      (∀ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), ∀ v ∈ V, m v ∈ U₀) ∧
      ∀ C : Subgroup W,
        (∀ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), ∀ v ∈ V, m v ∈ C) → U₀ ≤ C := by
    refine ⟨Subgroup.closure {w | ∃ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      ∃ v ∈ V, m v = w}, fun m hm v hv => Subgroup.subset_closure ⟨m, hm, v, hv, rfl⟩,
      fun C hC => ?_⟩
    rw [Subgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    exact hC m hm v hv
  have hU0Lt : U₀ ≤ fixV (conjAutSub t L) := by
    refine hU0le _ fun m hm v hv x hx => ?_
    obtain ⟨hmM, hmL⟩ := (hmemP m).mp hm
    have hx' : m⁻¹ * x * m ∈ conjAutSub t L := by
      have : x ∈ conjAutSub m (conjAutSub t L) := by
        rw [hPLt m hmM hmL]
        exact hx
      exact mem_conjAutSub_iff.mp this
    have e : x (m v) = m ((m⁻¹ * x * m) v) := by simp [MulAut.mul_apply]
    rw [e, htriv v hv _ hx']
  have hVU : V ≤ commV L := by
    calc V = commSub V L := hVL.symm
      _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl
      _ = commV L := (commV_eq_commSub L).symm
  have hU0comm : U₀ ≤ commV L := by
    refine hU0le _ fun m hm v hv => ?_
    exact d321a_commV_stable (Subgroup.mem_inf.mp hm).2 (hVU hv)
  have hU0L : ∀ l ∈ L, ∀ u ∈ U₀, l u ∈ U₀ := by
    intro l hl u hu
    have hlP : l ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_inf.mpr ⟨hLM hl, Subgroup.le_normalizer hl⟩
    have h : U₀ ≤ U₀.comap l.toMonoidHom := by
      refine hU0le _ fun m hm v hv => ?_
      rw [Subgroup.mem_comap]
      exact hU0mem (l * m) ((M ⊓ Subgroup.normalizer (L : Set (MulAut W))).mul_mem hlP hm) v hv
    exact Subgroup.mem_comap.mp (h hu)
  have hgenle : (⊤ : Subgroup W) ≤ U₀ ⊔ U₀.map t.toMonoidHom := by
    refine hgen.symm.le.trans (iSup₂_le fun g hg => ?_)
    rintro _ ⟨v, hv, rfl⟩
    rcases hsplit g hg with h | h
    · exact Subgroup.mem_sup_left (hU0mem g ((hmemP g).mpr ⟨hg, h⟩) v hv)
    · refine Subgroup.mem_sup_right ⟨(t⁻¹ * g) v,
        hU0mem _ ((hmemP _).mpr ⟨M.mul_mem (M.inv_mem htM) hg, h⟩) v hv, ?_⟩
      simp [MulAut.mul_apply]
  have hbL : ∀ b ∈ U₀.map t.toMonoidHom, ∀ l ∈ L, l b = b := by
    rintro _ ⟨u, hu, rfl⟩ l hl
    have hy : t⁻¹ * l * t ∈ conjAutSub t L := by
      rw [← hti, mem_conjAutSub_iff]
      have e : t⁻¹⁻¹ * (t⁻¹ * l * t) * t⁻¹ = l := by group
      rw [e]
      exact hl
    have hfix : (t⁻¹ * l * t) u = u := hU0Lt hu _ hy
    show l (t u) = t u
    have e : l (t u) = t ((t⁻¹ * l * t) u) := by simp [MulAut.mul_apply]
    rw [e, hfix]
  have hUle : commV L ≤ U₀ := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hgenle (Subgroup.mem_top w))
    have e : l (a * b) * (a * b)⁻¹ = l a * a⁻¹ := by
      rw [map_mul, hbL b hb l hl, mul_inv_rev]
      group
    rw [e]
    exact U₀.mul_mem (hU0L l hl a ha) (U₀.inv_mem ha)
  have hU : commV L = U₀ := le_antisymm hUle hU0comm
  rw [hU]
  refine ⟨⟨(eq_top_iff.mpr (hgenle.trans le_sup_left)).symm, ?_⟩, hU0Lt⟩
  intro x hx
  obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.mp hx.1
  obtain ⟨b, hb, c', hc', hbc⟩ := Subgroup.mem_sup.mp hx.2
  have haL : ∀ l ∈ L, l a = a := by
    intro l hl
    have h1 : l (a * c) = l (b * c') := by rw [hac, hbc]
    rw [map_mul, map_mul, hbL b hb l hl, hc' l (hLMp hl), hc l (hLMp hl)] at h1
    exact mul_right_cancel (h1.trans (hbc.trans hac.symm))
  have ha' : a ∈ fixV Mp := by
    rw [hMp, d321a_fixV_sup]
    exact ⟨haL, hU0Lt ha⟩
  rw [← hac]
  exact (fixV Mp).mul_mem ha' hc

theorem d321_struct (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
      commV L ≤ fixV (conjAutSub t L) := by
  obtain ⟨hA38, hcomm, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hLs : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hD := hstd.hyp
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hD.quasi.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  exact d321a_core hD.gen (le_of_mem_cComp hD.comp) (hD.sylow.1 htT)
    (fun g hg => d321a_perm hLs hnab hcomm hMp hD.Mp_normal hg) htL hMp
    (d321_comm_eq hstd hMp htriv) htriv

end Helpers

end CFSG.Quasithin
